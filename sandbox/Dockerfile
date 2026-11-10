# The sandbox image for container mode: Python with numpy and CPU-only torch,
# nothing else. Recipes run in it as nobody, with no network and a read-only
# root filesystem; only the sandbox folder is mounted.
#
# Build it with `python -m core.sandbox build`, which passes this machine's
# Python version and the numpy and torch versions installed here (the pins in
# requirements.txt only when one is not installed).
ARG PYTHON_VERSION=3.13
FROM python:${PYTHON_VERSION}-slim

ARG NUMPY_VERSION
ARG TORCH_VERSION
# A current pip first: older ones reject torch's dependencies as the PyTorch
# index names them. PyPI is the fallback for those dependencies; torch itself
# comes from the CPU index, whose +cpu build pip prefers at the pinned version.
RUN pip install --no-cache-dir --upgrade pip \
 && pip install --no-cache-dir "numpy==${NUMPY_VERSION}" \
 && pip install --no-cache-dir "torch==${TORCH_VERSION}" \
      --index-url https://download.pytorch.org/whl/cpu --extra-index-url https://pypi.org/simple \
 && rm -rf /root/.cache

WORKDIR /box
