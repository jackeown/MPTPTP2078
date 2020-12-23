%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:11 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  142 (2450 expanded)
%              Number of leaves         :   25 ( 670 expanded)
%              Depth                    :   44
%              Number of atoms          :  327 (8332 expanded)
%              Number of equality atoms :   58 ( 713 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3861,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3855,f106])).

fof(f106,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f104,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f102,f103])).

fof(f103,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f101,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f101,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f55,f96])).

fof(f96,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f54,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f55,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f56,f96])).

fof(f56,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f3855,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f3851,f1706])).

fof(f1706,plain,(
    ! [X11] :
      ( r2_hidden(sK3(X11),X11)
      | k1_xboole_0 = X11 ) ),
    inference(forward_demodulation,[],[f1536,f1532])).

fof(f1532,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f1397,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1397,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k3_xboole_0(k1_xboole_0,X1) = X0 ) ),
    inference(resolution,[],[f1386,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f1386,plain,(
    ! [X2] : v1_xboole_0(k3_xboole_0(k1_xboole_0,X2)) ),
    inference(resolution,[],[f1383,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1383,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k3_xboole_0(k1_xboole_0,X3)) ),
    inference(resolution,[],[f1377,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1377,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f1301,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1301,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(k1_xboole_0,sK0),X0)
      | r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f1292,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1292,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X0),X1) ),
    inference(resolution,[],[f630,f63])).

fof(f630,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(k1_xboole_0,sK0))
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f624,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f624,plain,(
    ! [X3] : r1_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X3) ),
    inference(resolution,[],[f599,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f599,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k3_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X0)) ),
    inference(superposition,[],[f309,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f309,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k3_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f301,f74])).

fof(f301,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f294,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f294,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f167,f114])).

fof(f114,plain,(
    ! [X1] : r1_xboole_0(sK1,k4_xboole_0(X1,sK0)) ),
    inference(resolution,[],[f108,f85])).

fof(f108,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f95,f89])).

fof(f89,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f95,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f91,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f159,f87])).

fof(f159,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f63,f115])).

fof(f115,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f108,f82])).

fof(f1536,plain,(
    ! [X10,X11] :
      ( k3_xboole_0(k1_xboole_0,X10) = X11
      | r2_hidden(sK3(X11),X11) ) ),
    inference(resolution,[],[f1397,f62])).

fof(f3851,plain,(
    ! [X16] : ~ r2_hidden(X16,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f3835,f63])).

fof(f3835,plain,(
    ! [X16] :
      ( ~ r2_hidden(X16,k4_xboole_0(sK1,sK2))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ) ),
    inference(resolution,[],[f3725,f1013])).

fof(f1013,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k4_xboole_0(sK1,sK2))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f1007,f87])).

fof(f1007,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f991,f73])).

fof(f991,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f288,f137])).

fof(f137,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f103,f86])).

fof(f288,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(sK0,X2)
      | ~ r2_hidden(X3,k3_xboole_0(sK1,X2)) ) ),
    inference(resolution,[],[f113,f74])).

fof(f113,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f108,f87])).

fof(f3725,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X1,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(forward_demodulation,[],[f3644,f3649])).

fof(f3649,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(backward_demodulation,[],[f3203,f3647])).

fof(f3647,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f3632,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3632,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1) ),
    inference(superposition,[],[f3203,f65])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f3203,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k3_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f3011,f3191])).

fof(f3191,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(resolution,[],[f3162,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3162,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f63,f2745])).

fof(f2745,plain,(
    ! [X4] : k4_xboole_0(X4,sK3(k1_zfmisc_1(k1_xboole_0))) = X4 ),
    inference(forward_demodulation,[],[f2742,f60])).

fof(f2742,plain,(
    ! [X4] : k4_xboole_0(X4,sK3(k1_zfmisc_1(k1_xboole_0))) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f66,f2189])).

fof(f2189,plain,(
    ! [X12] : k1_xboole_0 = k3_xboole_0(X12,sK3(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f2167,f1575])).

fof(f1575,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f1397,f1532])).

fof(f2167,plain,(
    ! [X0] : v1_xboole_0(k3_xboole_0(X0,sK3(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(superposition,[],[f2147,f64])).

fof(f2147,plain,(
    ! [X2] : v1_xboole_0(k3_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X2)) ),
    inference(resolution,[],[f1528,f62])).

fof(f1528,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k3_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X3)) ),
    inference(resolution,[],[f1526,f74])).

fof(f1526,plain,(
    ! [X5] : r1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X5) ),
    inference(subsumption_resolution,[],[f1519,f58])).

fof(f1519,plain,(
    ! [X5] :
      ( r1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X5)
      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f1426,f62])).

fof(f1426,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,k1_zfmisc_1(k1_xboole_0))
      | r1_xboole_0(X7,X8) ) ),
    inference(resolution,[],[f1382,f89])).

fof(f1382,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f1377,f87])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f3011,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X2,X2)) ),
    inference(superposition,[],[f68,f2987])).

fof(f2987,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f2974,f60])).

fof(f2974,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f2138,f65])).

fof(f2138,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    inference(forward_demodulation,[],[f2137,f1532])).

fof(f2137,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    inference(superposition,[],[f68,f2106])).

fof(f2106,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(resolution,[],[f2099,f75])).

fof(f2099,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(trivial_inequality_removal,[],[f2076])).

fof(f2076,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f81,f1956])).

fof(f1956,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f1953,f60])).

fof(f1953,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f66,f1532])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f3644,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k1_xboole_0,X1))
      | ~ r1_xboole_0(X1,X1) ) ),
    inference(superposition,[],[f74,f3203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:34:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (9919)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (9911)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (9903)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (9896)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (9899)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (9897)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (9908)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (9898)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (9901)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (9923)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (9905)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (9920)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (9914)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (9924)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (9917)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (9915)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (9900)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (9921)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (9906)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (9904)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (9909)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (9913)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (9907)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (9922)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (9925)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (9916)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (9912)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (9902)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.73/0.59  % (9918)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.73/0.60  % (9910)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.73/0.61  % (9918)Refutation not found, incomplete strategy% (9918)------------------------------
% 1.73/0.61  % (9918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (9918)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.61  
% 1.89/0.61  % (9918)Memory used [KB]: 10746
% 1.89/0.61  % (9918)Time elapsed: 0.165 s
% 1.89/0.61  % (9918)------------------------------
% 1.89/0.61  % (9918)------------------------------
% 2.81/0.75  % (9919)Refutation found. Thanks to Tanya!
% 2.81/0.75  % SZS status Theorem for theBenchmark
% 2.81/0.76  % SZS output start Proof for theBenchmark
% 2.81/0.76  fof(f3861,plain,(
% 2.81/0.76    $false),
% 2.81/0.76    inference(subsumption_resolution,[],[f3855,f106])).
% 2.81/0.76  fof(f106,plain,(
% 2.81/0.76    k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 2.81/0.76    inference(resolution,[],[f104,f81])).
% 2.81/0.76  fof(f81,plain,(
% 2.81/0.76    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f52])).
% 2.81/0.76  fof(f52,plain,(
% 2.81/0.76    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.81/0.76    inference(nnf_transformation,[],[f6])).
% 2.81/0.76  fof(f6,axiom,(
% 2.81/0.76    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.81/0.76  fof(f104,plain,(
% 2.81/0.76    ~r1_tarski(sK1,sK2)),
% 2.81/0.76    inference(subsumption_resolution,[],[f102,f103])).
% 2.81/0.76  fof(f103,plain,(
% 2.81/0.76    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.81/0.76    inference(subsumption_resolution,[],[f101,f85])).
% 2.81/0.76  fof(f85,plain,(
% 2.81/0.76    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f32])).
% 2.81/0.76  fof(f32,plain,(
% 2.81/0.76    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.81/0.76    inference(ennf_transformation,[],[f15])).
% 2.81/0.76  fof(f15,axiom,(
% 2.81/0.76    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.81/0.76  fof(f101,plain,(
% 2.81/0.76    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | r1_tarski(sK1,sK2)),
% 2.81/0.76    inference(backward_demodulation,[],[f55,f96])).
% 2.81/0.76  fof(f96,plain,(
% 2.81/0.76    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 2.81/0.76    inference(resolution,[],[f54,f76])).
% 2.81/0.76  fof(f76,plain,(
% 2.81/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.81/0.76    inference(cnf_transformation,[],[f30])).
% 2.81/0.76  fof(f30,plain,(
% 2.81/0.76    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.76    inference(ennf_transformation,[],[f21])).
% 2.81/0.76  fof(f21,axiom,(
% 2.81/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.81/0.76  fof(f54,plain,(
% 2.81/0.76    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.81/0.76    inference(cnf_transformation,[],[f40])).
% 2.81/0.76  fof(f40,plain,(
% 2.81/0.76    ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.81/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f39,f38])).
% 2.81/0.76  fof(f38,plain,(
% 2.81/0.76    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.81/0.76    introduced(choice_axiom,[])).
% 2.81/0.76  fof(f39,plain,(
% 2.81/0.76    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.81/0.76    introduced(choice_axiom,[])).
% 2.81/0.76  fof(f37,plain,(
% 2.81/0.76    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.76    inference(flattening,[],[f36])).
% 2.81/0.76  fof(f36,plain,(
% 2.81/0.76    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.76    inference(nnf_transformation,[],[f26])).
% 2.81/0.76  fof(f26,plain,(
% 2.81/0.76    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.76    inference(ennf_transformation,[],[f24])).
% 2.81/0.76  fof(f24,negated_conjecture,(
% 2.81/0.76    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 2.81/0.76    inference(negated_conjecture,[],[f23])).
% 2.81/0.76  fof(f23,conjecture,(
% 2.81/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 2.81/0.76  fof(f55,plain,(
% 2.81/0.76    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 2.81/0.76    inference(cnf_transformation,[],[f40])).
% 2.81/0.76  fof(f102,plain,(
% 2.81/0.76    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~r1_tarski(sK1,sK2)),
% 2.81/0.76    inference(backward_demodulation,[],[f56,f96])).
% 2.81/0.76  fof(f56,plain,(
% 2.81/0.76    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 2.81/0.76    inference(cnf_transformation,[],[f40])).
% 2.81/0.76  fof(f3855,plain,(
% 2.81/0.76    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.81/0.76    inference(resolution,[],[f3851,f1706])).
% 2.81/0.76  fof(f1706,plain,(
% 2.81/0.76    ( ! [X11] : (r2_hidden(sK3(X11),X11) | k1_xboole_0 = X11) )),
% 2.81/0.76    inference(forward_demodulation,[],[f1536,f1532])).
% 2.81/0.76  fof(f1532,plain,(
% 2.81/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.81/0.76    inference(resolution,[],[f1397,f57])).
% 2.81/0.76  fof(f57,plain,(
% 2.81/0.76    v1_xboole_0(k1_xboole_0)),
% 2.81/0.76    inference(cnf_transformation,[],[f4])).
% 2.81/0.76  fof(f4,axiom,(
% 2.81/0.76    v1_xboole_0(k1_xboole_0)),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.81/0.76  fof(f1397,plain,(
% 2.81/0.76    ( ! [X0,X1] : (~v1_xboole_0(X0) | k3_xboole_0(k1_xboole_0,X1) = X0) )),
% 2.81/0.76    inference(resolution,[],[f1386,f83])).
% 2.81/0.76  fof(f83,plain,(
% 2.81/0.76    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f31])).
% 2.81/0.76  fof(f31,plain,(
% 2.81/0.76    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.81/0.76    inference(ennf_transformation,[],[f16])).
% 2.81/0.76  fof(f16,axiom,(
% 2.81/0.76    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.81/0.76  fof(f1386,plain,(
% 2.81/0.76    ( ! [X2] : (v1_xboole_0(k3_xboole_0(k1_xboole_0,X2))) )),
% 2.81/0.76    inference(resolution,[],[f1383,f62])).
% 2.81/0.76  fof(f62,plain,(
% 2.81/0.76    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f44])).
% 2.81/0.76  fof(f44,plain,(
% 2.81/0.76    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.81/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 2.81/0.76  fof(f43,plain,(
% 2.81/0.76    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.81/0.76    introduced(choice_axiom,[])).
% 2.81/0.76  fof(f42,plain,(
% 2.81/0.76    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.81/0.76    inference(rectify,[],[f41])).
% 2.81/0.76  fof(f41,plain,(
% 2.81/0.76    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.81/0.76    inference(nnf_transformation,[],[f3])).
% 2.81/0.76  fof(f3,axiom,(
% 2.81/0.76    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.81/0.76  fof(f1383,plain,(
% 2.81/0.76    ( ! [X2,X3] : (~r2_hidden(X2,k3_xboole_0(k1_xboole_0,X3))) )),
% 2.81/0.76    inference(resolution,[],[f1377,f74])).
% 2.81/0.76  fof(f74,plain,(
% 2.81/0.76    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.81/0.76    inference(cnf_transformation,[],[f47])).
% 2.81/0.76  fof(f47,plain,(
% 2.81/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.81/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f46])).
% 2.81/0.76  fof(f46,plain,(
% 2.81/0.76    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.81/0.76    introduced(choice_axiom,[])).
% 2.81/0.76  fof(f28,plain,(
% 2.81/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.81/0.76    inference(ennf_transformation,[],[f25])).
% 2.81/0.76  fof(f25,plain,(
% 2.81/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.76    inference(rectify,[],[f5])).
% 2.81/0.76  fof(f5,axiom,(
% 2.81/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.81/0.76  fof(f1377,plain,(
% 2.81/0.76    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.81/0.76    inference(resolution,[],[f1301,f63])).
% 2.81/0.76  fof(f63,plain,(
% 2.81/0.76    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f10])).
% 2.81/0.76  fof(f10,axiom,(
% 2.81/0.76    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.81/0.76  fof(f1301,plain,(
% 2.81/0.76    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(k1_xboole_0,sK0),X0) | r1_xboole_0(k1_xboole_0,X1)) )),
% 2.81/0.76    inference(superposition,[],[f1292,f82])).
% 2.81/0.76  fof(f82,plain,(
% 2.81/0.76    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f52])).
% 2.81/0.76  fof(f1292,plain,(
% 2.81/0.76    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X0),X1)) )),
% 2.81/0.76    inference(resolution,[],[f630,f63])).
% 2.81/0.76  fof(f630,plain,(
% 2.81/0.76    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(k1_xboole_0,sK0)) | r1_xboole_0(X0,X1)) )),
% 2.81/0.76    inference(resolution,[],[f624,f87])).
% 2.81/0.76  fof(f87,plain,(
% 2.81/0.76    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f35])).
% 2.81/0.76  fof(f35,plain,(
% 2.81/0.76    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.81/0.76    inference(flattening,[],[f34])).
% 2.81/0.76  fof(f34,plain,(
% 2.81/0.76    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.81/0.76    inference(ennf_transformation,[],[f13])).
% 2.81/0.76  fof(f13,axiom,(
% 2.81/0.76    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.81/0.76  fof(f624,plain,(
% 2.81/0.76    ( ! [X3] : (r1_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X3)) )),
% 2.81/0.76    inference(resolution,[],[f599,f73])).
% 2.81/0.76  fof(f73,plain,(
% 2.81/0.76    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f47])).
% 2.81/0.76  fof(f599,plain,(
% 2.81/0.76    ( ! [X0,X1] : (~r2_hidden(X1,k3_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X0))) )),
% 2.81/0.76    inference(superposition,[],[f309,f64])).
% 2.81/0.76  fof(f64,plain,(
% 2.81/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f1])).
% 2.81/0.76  fof(f1,axiom,(
% 2.81/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.81/0.76  fof(f309,plain,(
% 2.81/0.76    ( ! [X4,X3] : (~r2_hidden(X3,k3_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK0)))) )),
% 2.81/0.76    inference(resolution,[],[f301,f74])).
% 2.81/0.76  fof(f301,plain,(
% 2.81/0.76    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,sK0))) )),
% 2.81/0.76    inference(resolution,[],[f294,f86])).
% 2.81/0.76  fof(f86,plain,(
% 2.81/0.76    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 2.81/0.76    inference(cnf_transformation,[],[f33])).
% 2.81/0.76  fof(f33,plain,(
% 2.81/0.76    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.81/0.76    inference(ennf_transformation,[],[f14])).
% 2.81/0.76  fof(f14,axiom,(
% 2.81/0.76    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 2.81/0.76  fof(f294,plain,(
% 2.81/0.76    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) )),
% 2.81/0.76    inference(resolution,[],[f167,f114])).
% 2.81/0.76  fof(f114,plain,(
% 2.81/0.76    ( ! [X1] : (r1_xboole_0(sK1,k4_xboole_0(X1,sK0))) )),
% 2.81/0.76    inference(resolution,[],[f108,f85])).
% 2.81/0.76  fof(f108,plain,(
% 2.81/0.76    r1_tarski(sK1,sK0)),
% 2.81/0.76    inference(resolution,[],[f95,f89])).
% 2.81/0.76  fof(f89,plain,(
% 2.81/0.76    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.81/0.76    inference(equality_resolution,[],[f77])).
% 2.81/0.76  fof(f77,plain,(
% 2.81/0.76    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.81/0.76    inference(cnf_transformation,[],[f51])).
% 2.81/0.76  fof(f51,plain,(
% 2.81/0.76    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.81/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 2.81/0.76  fof(f50,plain,(
% 2.81/0.76    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 2.81/0.76    introduced(choice_axiom,[])).
% 2.81/0.76  fof(f49,plain,(
% 2.81/0.76    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.81/0.76    inference(rectify,[],[f48])).
% 2.81/0.76  fof(f48,plain,(
% 2.81/0.76    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.81/0.76    inference(nnf_transformation,[],[f19])).
% 2.81/0.76  fof(f19,axiom,(
% 2.81/0.76    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.81/0.76  fof(f95,plain,(
% 2.81/0.76    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.81/0.76    inference(subsumption_resolution,[],[f91,f58])).
% 2.81/0.76  fof(f58,plain,(
% 2.81/0.76    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.81/0.76    inference(cnf_transformation,[],[f22])).
% 2.81/0.76  fof(f22,axiom,(
% 2.81/0.76    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.81/0.76  fof(f91,plain,(
% 2.81/0.76    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.81/0.76    inference(resolution,[],[f53,f69])).
% 2.81/0.76  fof(f69,plain,(
% 2.81/0.76    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.81/0.76    inference(cnf_transformation,[],[f45])).
% 2.81/0.76  fof(f45,plain,(
% 2.81/0.76    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.81/0.76    inference(nnf_transformation,[],[f27])).
% 2.81/0.76  fof(f27,plain,(
% 2.81/0.76    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.81/0.76    inference(ennf_transformation,[],[f20])).
% 2.81/0.76  fof(f20,axiom,(
% 2.81/0.76    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.81/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.81/0.76  fof(f53,plain,(
% 2.81/0.76    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.81/0.76    inference(cnf_transformation,[],[f40])).
% 2.81/0.76  fof(f167,plain,(
% 2.81/0.76    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 2.81/0.76    inference(resolution,[],[f159,f87])).
% 2.81/0.76  fof(f159,plain,(
% 2.81/0.76    r1_tarski(k1_xboole_0,sK1)),
% 2.81/0.76    inference(superposition,[],[f63,f115])).
% 2.81/0.76  fof(f115,plain,(
% 2.81/0.76    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 2.81/0.76    inference(resolution,[],[f108,f82])).
% 2.81/0.77  fof(f1536,plain,(
% 2.81/0.77    ( ! [X10,X11] : (k3_xboole_0(k1_xboole_0,X10) = X11 | r2_hidden(sK3(X11),X11)) )),
% 2.81/0.77    inference(resolution,[],[f1397,f62])).
% 2.81/0.77  fof(f3851,plain,(
% 2.81/0.77    ( ! [X16] : (~r2_hidden(X16,k4_xboole_0(sK1,sK2))) )),
% 2.81/0.77    inference(subsumption_resolution,[],[f3835,f63])).
% 2.81/0.77  fof(f3835,plain,(
% 2.81/0.77    ( ! [X16] : (~r2_hidden(X16,k4_xboole_0(sK1,sK2)) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1)) )),
% 2.81/0.77    inference(resolution,[],[f3725,f1013])).
% 2.81/0.77  fof(f1013,plain,(
% 2.81/0.77    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK1,sK2)) | ~r1_tarski(X0,sK1)) )),
% 2.81/0.77    inference(resolution,[],[f1007,f87])).
% 2.81/0.77  fof(f1007,plain,(
% 2.81/0.77    r1_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.81/0.77    inference(resolution,[],[f991,f73])).
% 2.81/0.77  fof(f991,plain,(
% 2.81/0.77    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) )),
% 2.81/0.77    inference(resolution,[],[f288,f137])).
% 2.81/0.77  fof(f137,plain,(
% 2.81/0.77    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.81/0.77    inference(resolution,[],[f103,f86])).
% 2.81/0.77  fof(f288,plain,(
% 2.81/0.77    ( ! [X2,X3] : (~r1_xboole_0(sK0,X2) | ~r2_hidden(X3,k3_xboole_0(sK1,X2))) )),
% 2.81/0.77    inference(resolution,[],[f113,f74])).
% 2.81/0.77  fof(f113,plain,(
% 2.81/0.77    ( ! [X0] : (r1_xboole_0(sK1,X0) | ~r1_xboole_0(sK0,X0)) )),
% 2.81/0.77    inference(resolution,[],[f108,f87])).
% 2.81/0.77  fof(f3725,plain,(
% 2.81/0.77    ( ! [X2,X1] : (~r1_xboole_0(X1,X1) | ~r2_hidden(X2,X1)) )),
% 2.81/0.77    inference(forward_demodulation,[],[f3644,f3649])).
% 2.81/0.77  fof(f3649,plain,(
% 2.81/0.77    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = X2) )),
% 2.81/0.77    inference(backward_demodulation,[],[f3203,f3647])).
% 2.81/0.77  fof(f3647,plain,(
% 2.81/0.77    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 2.81/0.77    inference(forward_demodulation,[],[f3632,f60])).
% 2.81/0.77  fof(f60,plain,(
% 2.81/0.77    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.81/0.77    inference(cnf_transformation,[],[f12])).
% 2.81/0.77  fof(f12,axiom,(
% 2.81/0.77    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.81/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.81/0.77  fof(f3632,plain,(
% 2.81/0.77    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1)) )),
% 2.81/0.77    inference(superposition,[],[f3203,f65])).
% 2.81/0.77  fof(f65,plain,(
% 2.81/0.77    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.81/0.77    inference(cnf_transformation,[],[f2])).
% 2.81/0.77  fof(f2,axiom,(
% 2.81/0.77    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.81/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.81/0.77  fof(f3203,plain,(
% 2.81/0.77    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k3_xboole_0(X2,X2)) )),
% 2.81/0.77    inference(backward_demodulation,[],[f3011,f3191])).
% 2.81/0.77  fof(f3191,plain,(
% 2.81/0.77    ( ! [X6] : (k2_xboole_0(X6,X6) = X6) )),
% 2.81/0.77    inference(resolution,[],[f3162,f75])).
% 2.81/0.77  fof(f75,plain,(
% 2.81/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.81/0.77    inference(cnf_transformation,[],[f29])).
% 2.81/0.77  fof(f29,plain,(
% 2.81/0.77    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.81/0.77    inference(ennf_transformation,[],[f8])).
% 2.81/0.77  fof(f8,axiom,(
% 2.81/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.81/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.81/0.77  fof(f3162,plain,(
% 2.81/0.77    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.81/0.77    inference(superposition,[],[f63,f2745])).
% 2.81/0.77  fof(f2745,plain,(
% 2.81/0.77    ( ! [X4] : (k4_xboole_0(X4,sK3(k1_zfmisc_1(k1_xboole_0))) = X4) )),
% 2.81/0.77    inference(forward_demodulation,[],[f2742,f60])).
% 2.81/0.77  fof(f2742,plain,(
% 2.81/0.77    ( ! [X4] : (k4_xboole_0(X4,sK3(k1_zfmisc_1(k1_xboole_0))) = k5_xboole_0(X4,k1_xboole_0)) )),
% 2.81/0.77    inference(superposition,[],[f66,f2189])).
% 2.81/0.77  fof(f2189,plain,(
% 2.81/0.77    ( ! [X12] : (k1_xboole_0 = k3_xboole_0(X12,sK3(k1_zfmisc_1(k1_xboole_0)))) )),
% 2.81/0.77    inference(resolution,[],[f2167,f1575])).
% 2.81/0.77  fof(f1575,plain,(
% 2.81/0.77    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.81/0.77    inference(backward_demodulation,[],[f1397,f1532])).
% 2.81/0.77  fof(f2167,plain,(
% 2.81/0.77    ( ! [X0] : (v1_xboole_0(k3_xboole_0(X0,sK3(k1_zfmisc_1(k1_xboole_0))))) )),
% 2.81/0.77    inference(superposition,[],[f2147,f64])).
% 2.81/0.77  fof(f2147,plain,(
% 2.81/0.77    ( ! [X2] : (v1_xboole_0(k3_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X2))) )),
% 2.81/0.77    inference(resolution,[],[f1528,f62])).
% 2.81/0.77  fof(f1528,plain,(
% 2.81/0.77    ( ! [X2,X3] : (~r2_hidden(X2,k3_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X3))) )),
% 2.81/0.77    inference(resolution,[],[f1526,f74])).
% 2.81/0.77  fof(f1526,plain,(
% 2.81/0.77    ( ! [X5] : (r1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X5)) )),
% 2.81/0.77    inference(subsumption_resolution,[],[f1519,f58])).
% 2.81/0.77  fof(f1519,plain,(
% 2.81/0.77    ( ! [X5] : (r1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)),X5) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))) )),
% 2.81/0.77    inference(resolution,[],[f1426,f62])).
% 2.81/0.77  fof(f1426,plain,(
% 2.81/0.77    ( ! [X8,X7] : (~r2_hidden(X7,k1_zfmisc_1(k1_xboole_0)) | r1_xboole_0(X7,X8)) )),
% 2.81/0.77    inference(resolution,[],[f1382,f89])).
% 2.81/0.77  fof(f1382,plain,(
% 2.81/0.77    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_xboole_0(X0,X1)) )),
% 2.81/0.77    inference(resolution,[],[f1377,f87])).
% 2.81/0.77  fof(f66,plain,(
% 2.81/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.81/0.77    inference(cnf_transformation,[],[f7])).
% 2.81/0.77  fof(f7,axiom,(
% 2.81/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.81/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.81/0.77  fof(f3011,plain,(
% 2.81/0.77    ( ! [X2] : (k3_xboole_0(X2,X2) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X2,X2))) )),
% 2.81/0.77    inference(superposition,[],[f68,f2987])).
% 2.81/0.77  fof(f2987,plain,(
% 2.81/0.77    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.81/0.77    inference(forward_demodulation,[],[f2974,f60])).
% 2.81/0.77  fof(f2974,plain,(
% 2.81/0.77    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 2.81/0.77    inference(superposition,[],[f2138,f65])).
% 2.81/0.77  fof(f2138,plain,(
% 2.81/0.77    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) )),
% 2.81/0.77    inference(forward_demodulation,[],[f2137,f1532])).
% 2.81/0.77  fof(f2137,plain,(
% 2.81/0.77    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) )),
% 2.81/0.77    inference(superposition,[],[f68,f2106])).
% 2.81/0.77  fof(f2106,plain,(
% 2.81/0.77    ( ! [X7] : (k2_xboole_0(k1_xboole_0,X7) = X7) )),
% 2.81/0.77    inference(resolution,[],[f2099,f75])).
% 2.81/0.77  fof(f2099,plain,(
% 2.81/0.77    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.81/0.77    inference(trivial_inequality_removal,[],[f2076])).
% 2.81/0.77  fof(f2076,plain,(
% 2.81/0.77    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X2)) )),
% 2.81/0.77    inference(superposition,[],[f81,f1956])).
% 2.81/0.77  fof(f1956,plain,(
% 2.81/0.77    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 2.81/0.77    inference(forward_demodulation,[],[f1953,f60])).
% 2.81/0.77  fof(f1953,plain,(
% 2.81/0.77    ( ! [X4] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X4)) )),
% 2.81/0.77    inference(superposition,[],[f66,f1532])).
% 2.81/0.77  fof(f68,plain,(
% 2.81/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.81/0.77    inference(cnf_transformation,[],[f18])).
% 2.81/0.77  fof(f18,axiom,(
% 2.81/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.81/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.81/0.77  fof(f3644,plain,(
% 2.81/0.77    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(k1_xboole_0,X1)) | ~r1_xboole_0(X1,X1)) )),
% 2.81/0.77    inference(superposition,[],[f74,f3203])).
% 2.81/0.77  % SZS output end Proof for theBenchmark
% 2.81/0.77  % (9919)------------------------------
% 2.81/0.77  % (9919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.77  % (9919)Termination reason: Refutation
% 2.81/0.77  
% 2.81/0.77  % (9919)Memory used [KB]: 2942
% 2.81/0.77  % (9919)Time elapsed: 0.258 s
% 2.81/0.77  % (9919)------------------------------
% 2.81/0.77  % (9919)------------------------------
% 2.81/0.77  % (9895)Success in time 0.404 s
%------------------------------------------------------------------------------
