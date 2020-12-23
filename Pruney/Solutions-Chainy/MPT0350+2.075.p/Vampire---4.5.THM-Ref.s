%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:01 EST 2020

% Result     : Theorem 5.44s
% Output     : Refutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 857 expanded)
%              Number of leaves         :   20 ( 235 expanded)
%              Depth                    :   23
%              Number of atoms          :  298 (2847 expanded)
%              Number of equality atoms :  107 ( 701 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7893,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7892,f2822])).

fof(f2822,plain,(
    sK0 != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f103,f2698])).

fof(f2698,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f2681,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f2681,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1542,f2679])).

fof(f2679,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(subsumption_resolution,[],[f2677,f340])).

fof(f340,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f334,f186])).

fof(f186,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k4_xboole_0(sK0,X3)) ) ),
    inference(resolution,[],[f136,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f136,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f84,f120])).

fof(f120,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f116,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f116,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f54,f111])).

fof(f111,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f104,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f104,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f97,f82])).

fof(f82,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f97,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f91,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f334,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,k4_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f85,f323])).

fof(f323,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f319,f49])).

fof(f319,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f54,f173])).

fof(f173,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f163,f60])).

fof(f163,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f153,f82])).

fof(f153,plain,(
    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f145,f47])).

fof(f145,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f96,f56])).

fof(f96,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f90,f89])).

fof(f89,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f90,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f45,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2677,plain,(
    ! [X2] :
      ( k1_xboole_0 = k4_xboole_0(X2,X2)
      | r2_hidden(sK3(X2,X2,k1_xboole_0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f2651])).

fof(f2651,plain,(
    ! [X2] :
      ( k1_xboole_0 = k4_xboole_0(X2,X2)
      | k1_xboole_0 = k4_xboole_0(X2,X2)
      | r2_hidden(sK3(X2,X2,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f347,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f347,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK3(X10,X11,k1_xboole_0),X10)
      | k1_xboole_0 = k4_xboole_0(X10,X11) ) ),
    inference(resolution,[],[f340,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1542,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f466,f1532])).

fof(f1532,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f1517,f124])).

fof(f124,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f54,f112])).

fof(f112,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f111,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1517,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) ),
    inference(forward_demodulation,[],[f1510,f54])).

fof(f1510,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f130,f51])).

fof(f130,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f127,f51])).

fof(f127,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f69,f112])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f466,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f55,f309])).

fof(f309,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f305,f124])).

fof(f305,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f117,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f117,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f55,f111])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f103,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f102,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f101,f96])).

fof(f101,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f95,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f95,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f86,f89])).

fof(f86,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f46,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f46,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f7892,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f4496,f7891])).

fof(f7891,plain,(
    sK0 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f7874,f50])).

fof(f7874,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f1824,f49])).

fof(f1824,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),X0)) ),
    inference(superposition,[],[f68,f1757])).

fof(f1757,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1724,f309])).

fof(f1724,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f197,f49])).

fof(f197,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f68,f124])).

fof(f4496,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f3749,f309])).

fof(f3749,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f68,f3480])).

fof(f3480,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f3479,f1547])).

fof(f1547,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1546,f112])).

fof(f1546,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1534,f51])).

fof(f1534,plain,(
    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f1517,f50])).

fof(f3479,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3451,f49])).

fof(f3451,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f2056,f120])).

fof(f2056,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k5_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f2055,f1517])).

fof(f2055,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(sK1,X0),sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X0,sK0))) ),
    inference(forward_demodulation,[],[f2043,f68])).

fof(f2043,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,X0),sK0)) = k5_xboole_0(k4_xboole_0(sK1,X0),sK1) ),
    inference(superposition,[],[f1624,f1517])).

fof(f1624,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k5_xboole_0(k3_xboole_0(sK1,X1),sK1) ),
    inference(superposition,[],[f131,f51])).

fof(f131,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f128,f51])).

fof(f128,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1) ),
    inference(superposition,[],[f69,f112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (28036)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % (28043)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (28037)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (28035)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (28034)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (28055)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28047)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (28032)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28061)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (28033)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28031)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (28054)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (28056)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (28038)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (28045)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (28052)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (28050)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (28049)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (28053)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (28048)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (28049)Refutation not found, incomplete strategy% (28049)------------------------------
% 0.21/0.55  % (28049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28049)Memory used [KB]: 10618
% 0.21/0.55  % (28049)Time elapsed: 0.145 s
% 0.21/0.55  % (28049)------------------------------
% 0.21/0.55  % (28049)------------------------------
% 0.21/0.55  % (28046)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (28039)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (28044)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (28040)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (28042)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (28051)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (28060)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (28057)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (28058)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (28059)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (28054)Refutation not found, incomplete strategy% (28054)------------------------------
% 0.21/0.56  % (28054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28054)Memory used [KB]: 10746
% 0.21/0.56  % (28054)Time elapsed: 0.155 s
% 0.21/0.56  % (28054)------------------------------
% 0.21/0.56  % (28054)------------------------------
% 2.04/0.67  % (28166)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.69/0.71  % (28169)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.21/0.85  % (28036)Time limit reached!
% 3.21/0.85  % (28036)------------------------------
% 3.21/0.85  % (28036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.85  % (28036)Termination reason: Time limit
% 3.21/0.85  
% 3.21/0.85  % (28036)Memory used [KB]: 14072
% 3.21/0.85  % (28036)Time elapsed: 0.439 s
% 3.21/0.85  % (28036)------------------------------
% 3.21/0.85  % (28036)------------------------------
% 4.33/0.92  % (28044)Time limit reached!
% 4.33/0.92  % (28044)------------------------------
% 4.33/0.92  % (28044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.93  % (28032)Time limit reached!
% 4.43/0.93  % (28032)------------------------------
% 4.43/0.93  % (28032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.93  % (28032)Termination reason: Time limit
% 4.43/0.93  % (28032)Termination phase: Saturation
% 4.43/0.93  
% 4.43/0.93  % (28032)Memory used [KB]: 8187
% 4.43/0.93  % (28032)Time elapsed: 0.500 s
% 4.43/0.93  % (28032)------------------------------
% 4.43/0.93  % (28032)------------------------------
% 4.43/0.93  % (28044)Termination reason: Time limit
% 4.43/0.93  % (28044)Termination phase: Saturation
% 4.43/0.93  
% 4.43/0.93  % (28044)Memory used [KB]: 10234
% 4.43/0.93  % (28044)Time elapsed: 0.500 s
% 4.43/0.93  % (28044)------------------------------
% 4.43/0.93  % (28044)------------------------------
% 4.43/0.93  % (28031)Time limit reached!
% 4.43/0.93  % (28031)------------------------------
% 4.43/0.93  % (28031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.93  % (28031)Termination reason: Time limit
% 4.43/0.93  % (28031)Termination phase: Saturation
% 4.43/0.93  
% 4.43/0.93  % (28031)Memory used [KB]: 4733
% 4.43/0.93  % (28031)Time elapsed: 0.500 s
% 4.43/0.93  % (28031)------------------------------
% 4.43/0.93  % (28031)------------------------------
% 4.43/0.93  % (28042)Time limit reached!
% 4.43/0.93  % (28042)------------------------------
% 4.43/0.93  % (28042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.93  % (28042)Termination reason: Time limit
% 4.43/0.93  % (28042)Termination phase: Saturation
% 4.43/0.93  
% 4.43/0.93  % (28042)Memory used [KB]: 12920
% 4.43/0.93  % (28042)Time elapsed: 0.530 s
% 4.43/0.93  % (28042)------------------------------
% 4.43/0.93  % (28042)------------------------------
% 4.43/0.96  % (28246)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.97/1.02  % (28048)Time limit reached!
% 4.97/1.02  % (28048)------------------------------
% 4.97/1.02  % (28048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.02  % (28048)Termination reason: Time limit
% 4.97/1.02  
% 4.97/1.02  % (28048)Memory used [KB]: 16119
% 4.97/1.02  % (28048)Time elapsed: 0.618 s
% 4.97/1.02  % (28048)------------------------------
% 4.97/1.02  % (28048)------------------------------
% 4.97/1.04  % (28060)Time limit reached!
% 4.97/1.04  % (28060)------------------------------
% 4.97/1.04  % (28060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.05  % (28248)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.97/1.05  % (28249)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.97/1.05  % (28250)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.97/1.05  % (28247)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.97/1.05  % (28060)Termination reason: Time limit
% 4.97/1.05  
% 4.97/1.05  % (28060)Memory used [KB]: 9722
% 4.97/1.05  % (28060)Time elapsed: 0.637 s
% 4.97/1.05  % (28060)------------------------------
% 4.97/1.05  % (28060)------------------------------
% 4.97/1.06  % (28038)Time limit reached!
% 4.97/1.06  % (28038)------------------------------
% 4.97/1.06  % (28038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.06  % (28038)Termination reason: Time limit
% 4.97/1.06  % (28038)Termination phase: Saturation
% 4.97/1.06  
% 4.97/1.06  % (28038)Memory used [KB]: 12665
% 4.97/1.06  % (28038)Time elapsed: 0.600 s
% 4.97/1.06  % (28038)------------------------------
% 4.97/1.06  % (28038)------------------------------
% 5.44/1.12  % (28055)Refutation found. Thanks to Tanya!
% 5.44/1.12  % SZS status Theorem for theBenchmark
% 5.44/1.14  % SZS output start Proof for theBenchmark
% 5.44/1.14  fof(f7893,plain,(
% 5.44/1.14    $false),
% 5.44/1.14    inference(subsumption_resolution,[],[f7892,f2822])).
% 5.44/1.14  fof(f2822,plain,(
% 5.44/1.14    sK0 != k2_xboole_0(sK1,sK0)),
% 5.44/1.14    inference(superposition,[],[f103,f2698])).
% 5.44/1.14  fof(f2698,plain,(
% 5.44/1.14    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0)),
% 5.44/1.14    inference(forward_demodulation,[],[f2681,f50])).
% 5.44/1.14  fof(f50,plain,(
% 5.44/1.14    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.44/1.14    inference(cnf_transformation,[],[f6])).
% 5.44/1.14  fof(f6,axiom,(
% 5.44/1.14    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 5.44/1.14  fof(f2681,plain,(
% 5.44/1.14    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0)),
% 5.44/1.14    inference(backward_demodulation,[],[f1542,f2679])).
% 5.44/1.14  fof(f2679,plain,(
% 5.44/1.14    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 5.44/1.14    inference(subsumption_resolution,[],[f2677,f340])).
% 5.44/1.14  fof(f340,plain,(
% 5.44/1.14    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 5.44/1.14    inference(subsumption_resolution,[],[f334,f186])).
% 5.44/1.14  fof(f186,plain,(
% 5.44/1.14    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k4_xboole_0(sK0,X3))) )),
% 5.44/1.14    inference(resolution,[],[f136,f85])).
% 5.44/1.14  fof(f85,plain,(
% 5.44/1.14    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 5.44/1.14    inference(equality_resolution,[],[f71])).
% 5.44/1.14  fof(f71,plain,(
% 5.44/1.14    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.44/1.14    inference(cnf_transformation,[],[f44])).
% 5.44/1.14  fof(f44,plain,(
% 5.44/1.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.44/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 5.44/1.14  fof(f43,plain,(
% 5.44/1.14    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 5.44/1.14    introduced(choice_axiom,[])).
% 5.44/1.14  fof(f42,plain,(
% 5.44/1.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.44/1.14    inference(rectify,[],[f41])).
% 5.44/1.14  fof(f41,plain,(
% 5.44/1.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.44/1.14    inference(flattening,[],[f40])).
% 5.44/1.14  fof(f40,plain,(
% 5.44/1.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.44/1.14    inference(nnf_transformation,[],[f2])).
% 5.44/1.14  fof(f2,axiom,(
% 5.44/1.14    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.44/1.14  fof(f136,plain,(
% 5.44/1.14    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 5.44/1.14    inference(superposition,[],[f84,f120])).
% 5.44/1.14  fof(f120,plain,(
% 5.44/1.14    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 5.44/1.14    inference(forward_demodulation,[],[f116,f49])).
% 5.44/1.14  fof(f49,plain,(
% 5.44/1.14    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.44/1.14    inference(cnf_transformation,[],[f8])).
% 5.44/1.14  fof(f8,axiom,(
% 5.44/1.14    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.44/1.14  fof(f116,plain,(
% 5.44/1.14    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 5.44/1.14    inference(superposition,[],[f54,f111])).
% 5.44/1.14  fof(f111,plain,(
% 5.44/1.14    sK1 = k3_xboole_0(sK1,sK0)),
% 5.44/1.14    inference(resolution,[],[f104,f60])).
% 5.44/1.14  fof(f60,plain,(
% 5.44/1.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 5.44/1.14    inference(cnf_transformation,[],[f28])).
% 5.44/1.14  fof(f28,plain,(
% 5.44/1.14    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.44/1.14    inference(ennf_transformation,[],[f5])).
% 5.44/1.14  fof(f5,axiom,(
% 5.44/1.14    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.44/1.14  fof(f104,plain,(
% 5.44/1.14    r1_tarski(sK1,sK0)),
% 5.44/1.14    inference(resolution,[],[f97,f82])).
% 5.44/1.14  fof(f82,plain,(
% 5.44/1.14    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 5.44/1.14    inference(equality_resolution,[],[f63])).
% 5.44/1.14  fof(f63,plain,(
% 5.44/1.14    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 5.44/1.14    inference(cnf_transformation,[],[f39])).
% 5.44/1.14  fof(f39,plain,(
% 5.44/1.14    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 5.44/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 5.44/1.14  fof(f38,plain,(
% 5.44/1.14    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 5.44/1.14    introduced(choice_axiom,[])).
% 5.44/1.14  fof(f37,plain,(
% 5.44/1.14    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 5.44/1.14    inference(rectify,[],[f36])).
% 5.44/1.14  fof(f36,plain,(
% 5.44/1.14    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 5.44/1.14    inference(nnf_transformation,[],[f16])).
% 5.44/1.14  fof(f16,axiom,(
% 5.44/1.14    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 5.44/1.14  fof(f97,plain,(
% 5.44/1.14    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(subsumption_resolution,[],[f91,f47])).
% 5.44/1.14  fof(f47,plain,(
% 5.44/1.14    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 5.44/1.14    inference(cnf_transformation,[],[f22])).
% 5.44/1.14  fof(f22,axiom,(
% 5.44/1.14    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 5.44/1.14  fof(f91,plain,(
% 5.44/1.14    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(resolution,[],[f45,f56])).
% 5.44/1.14  fof(f56,plain,(
% 5.44/1.14    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 5.44/1.14    inference(cnf_transformation,[],[f35])).
% 5.44/1.14  fof(f35,plain,(
% 5.44/1.14    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 5.44/1.14    inference(nnf_transformation,[],[f27])).
% 5.44/1.14  fof(f27,plain,(
% 5.44/1.14    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 5.44/1.14    inference(ennf_transformation,[],[f18])).
% 5.44/1.14  fof(f18,axiom,(
% 5.44/1.14    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 5.44/1.14  fof(f45,plain,(
% 5.44/1.14    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(cnf_transformation,[],[f34])).
% 5.44/1.14  fof(f34,plain,(
% 5.44/1.14    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f33])).
% 5.44/1.14  fof(f33,plain,(
% 5.44/1.14    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 5.44/1.14    introduced(choice_axiom,[])).
% 5.44/1.14  fof(f26,plain,(
% 5.44/1.14    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.44/1.14    inference(ennf_transformation,[],[f25])).
% 5.44/1.14  fof(f25,negated_conjecture,(
% 5.44/1.14    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 5.44/1.14    inference(negated_conjecture,[],[f24])).
% 5.44/1.14  fof(f24,conjecture,(
% 5.44/1.14    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 5.44/1.14  fof(f54,plain,(
% 5.44/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.44/1.14    inference(cnf_transformation,[],[f3])).
% 5.44/1.14  fof(f3,axiom,(
% 5.44/1.14    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.44/1.14  fof(f84,plain,(
% 5.44/1.14    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 5.44/1.14    inference(equality_resolution,[],[f72])).
% 5.44/1.14  fof(f72,plain,(
% 5.44/1.14    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.44/1.14    inference(cnf_transformation,[],[f44])).
% 5.44/1.14  fof(f334,plain,(
% 5.44/1.14    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k4_xboole_0(sK0,sK1))) )),
% 5.44/1.14    inference(superposition,[],[f85,f323])).
% 5.44/1.14  fof(f323,plain,(
% 5.44/1.14    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 5.44/1.14    inference(forward_demodulation,[],[f319,f49])).
% 5.44/1.14  fof(f319,plain,(
% 5.44/1.14    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 5.44/1.14    inference(superposition,[],[f54,f173])).
% 5.44/1.14  fof(f173,plain,(
% 5.44/1.14    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 5.44/1.14    inference(resolution,[],[f163,f60])).
% 5.44/1.14  fof(f163,plain,(
% 5.44/1.14    r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 5.44/1.14    inference(resolution,[],[f153,f82])).
% 5.44/1.14  fof(f153,plain,(
% 5.44/1.14    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(subsumption_resolution,[],[f145,f47])).
% 5.44/1.14  fof(f145,plain,(
% 5.44/1.14    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(resolution,[],[f96,f56])).
% 5.44/1.14  fof(f96,plain,(
% 5.44/1.14    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(forward_demodulation,[],[f90,f89])).
% 5.44/1.14  fof(f89,plain,(
% 5.44/1.14    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 5.44/1.14    inference(resolution,[],[f45,f62])).
% 5.44/1.14  fof(f62,plain,(
% 5.44/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.44/1.14    inference(cnf_transformation,[],[f30])).
% 5.44/1.14  fof(f30,plain,(
% 5.44/1.14    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.44/1.14    inference(ennf_transformation,[],[f20])).
% 5.44/1.14  fof(f20,axiom,(
% 5.44/1.14    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 5.44/1.14  fof(f90,plain,(
% 5.44/1.14    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(resolution,[],[f45,f61])).
% 5.44/1.14  fof(f61,plain,(
% 5.44/1.14    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.44/1.14    inference(cnf_transformation,[],[f29])).
% 5.44/1.14  fof(f29,plain,(
% 5.44/1.14    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.44/1.14    inference(ennf_transformation,[],[f21])).
% 5.44/1.14  fof(f21,axiom,(
% 5.44/1.14    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 5.44/1.14  fof(f2677,plain,(
% 5.44/1.14    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2) | r2_hidden(sK3(X2,X2,k1_xboole_0),k1_xboole_0)) )),
% 5.44/1.14    inference(duplicate_literal_removal,[],[f2651])).
% 5.44/1.14  fof(f2651,plain,(
% 5.44/1.14    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2) | k1_xboole_0 = k4_xboole_0(X2,X2) | r2_hidden(sK3(X2,X2,k1_xboole_0),k1_xboole_0)) )),
% 5.44/1.14    inference(resolution,[],[f347,f75])).
% 5.44/1.14  fof(f75,plain,(
% 5.44/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 5.44/1.14    inference(cnf_transformation,[],[f44])).
% 5.44/1.14  fof(f347,plain,(
% 5.44/1.14    ( ! [X10,X11] : (r2_hidden(sK3(X10,X11,k1_xboole_0),X10) | k1_xboole_0 = k4_xboole_0(X10,X11)) )),
% 5.44/1.14    inference(resolution,[],[f340,f74])).
% 5.44/1.14  fof(f74,plain,(
% 5.44/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 5.44/1.14    inference(cnf_transformation,[],[f44])).
% 5.44/1.14  fof(f1542,plain,(
% 5.44/1.14    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1))),
% 5.44/1.14    inference(backward_demodulation,[],[f466,f1532])).
% 5.44/1.14  fof(f1532,plain,(
% 5.44/1.14    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK1)),
% 5.44/1.14    inference(superposition,[],[f1517,f124])).
% 5.44/1.14  fof(f124,plain,(
% 5.44/1.14    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 5.44/1.14    inference(superposition,[],[f54,f112])).
% 5.44/1.14  fof(f112,plain,(
% 5.44/1.14    sK1 = k3_xboole_0(sK0,sK1)),
% 5.44/1.14    inference(superposition,[],[f111,f51])).
% 5.44/1.14  fof(f51,plain,(
% 5.44/1.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.44/1.14    inference(cnf_transformation,[],[f1])).
% 5.44/1.14  fof(f1,axiom,(
% 5.44/1.14    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.44/1.14  fof(f1517,plain,(
% 5.44/1.14    ( ! [X1] : (k4_xboole_0(sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) )),
% 5.44/1.14    inference(forward_demodulation,[],[f1510,f54])).
% 5.44/1.14  fof(f1510,plain,(
% 5.44/1.14    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) )),
% 5.44/1.14    inference(superposition,[],[f130,f51])).
% 5.44/1.14  fof(f130,plain,(
% 5.44/1.14    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) )),
% 5.44/1.14    inference(forward_demodulation,[],[f127,f51])).
% 5.44/1.14  fof(f127,plain,(
% 5.44/1.14    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 5.44/1.14    inference(superposition,[],[f69,f112])).
% 5.44/1.14  fof(f69,plain,(
% 5.44/1.14    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 5.44/1.14    inference(cnf_transformation,[],[f4])).
% 5.44/1.14  fof(f4,axiom,(
% 5.44/1.14    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 5.44/1.14  fof(f466,plain,(
% 5.44/1.14    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 5.44/1.14    inference(superposition,[],[f55,f309])).
% 5.44/1.14  fof(f309,plain,(
% 5.44/1.14    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 5.44/1.14    inference(forward_demodulation,[],[f305,f124])).
% 5.44/1.14  fof(f305,plain,(
% 5.44/1.14    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 5.44/1.14    inference(superposition,[],[f117,f68])).
% 5.44/1.14  fof(f68,plain,(
% 5.44/1.14    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.44/1.14    inference(cnf_transformation,[],[f7])).
% 5.44/1.14  fof(f7,axiom,(
% 5.44/1.14    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.44/1.14  fof(f117,plain,(
% 5.44/1.14    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 5.44/1.14    inference(superposition,[],[f55,f111])).
% 5.44/1.14  fof(f55,plain,(
% 5.44/1.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.44/1.14    inference(cnf_transformation,[],[f9])).
% 5.44/1.14  fof(f9,axiom,(
% 5.44/1.14    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 5.44/1.14  fof(f103,plain,(
% 5.44/1.14    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 5.44/1.14    inference(subsumption_resolution,[],[f102,f45])).
% 5.44/1.14  fof(f102,plain,(
% 5.44/1.14    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(subsumption_resolution,[],[f101,f96])).
% 5.44/1.14  fof(f101,plain,(
% 5.44/1.14    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.44/1.14    inference(superposition,[],[f95,f70])).
% 5.44/1.14  fof(f70,plain,(
% 5.44/1.14    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.44/1.14    inference(cnf_transformation,[],[f32])).
% 5.44/1.14  fof(f32,plain,(
% 5.44/1.14    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.44/1.14    inference(flattening,[],[f31])).
% 5.44/1.14  fof(f31,plain,(
% 5.44/1.14    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.44/1.14    inference(ennf_transformation,[],[f23])).
% 5.44/1.14  fof(f23,axiom,(
% 5.44/1.14    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 5.44/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.44/1.14  fof(f95,plain,(
% 5.44/1.14    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 5.44/1.14    inference(backward_demodulation,[],[f86,f89])).
% 5.44/1.14  fof(f86,plain,(
% 5.44/1.14    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 5.44/1.14    inference(forward_demodulation,[],[f46,f48])).
% 5.44/1.14  fof(f48,plain,(
% 5.44/1.14    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 5.44/1.14    inference(cnf_transformation,[],[f19])).
% 5.44/1.15  fof(f19,axiom,(
% 5.44/1.15    ! [X0] : k2_subset_1(X0) = X0),
% 5.44/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 5.44/1.15  fof(f46,plain,(
% 5.44/1.15    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 5.44/1.15    inference(cnf_transformation,[],[f34])).
% 5.44/1.15  fof(f7892,plain,(
% 5.44/1.15    sK0 = k2_xboole_0(sK1,sK0)),
% 5.44/1.15    inference(backward_demodulation,[],[f4496,f7891])).
% 5.44/1.15  fof(f7891,plain,(
% 5.44/1.15    sK0 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0))),
% 5.44/1.15    inference(forward_demodulation,[],[f7874,f50])).
% 5.44/1.15  fof(f7874,plain,(
% 5.44/1.15    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0))),
% 5.44/1.15    inference(superposition,[],[f1824,f49])).
% 5.44/1.15  fof(f1824,plain,(
% 5.44/1.15    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),X0))) )),
% 5.44/1.15    inference(superposition,[],[f68,f1757])).
% 5.44/1.15  fof(f1757,plain,(
% 5.44/1.15    k1_xboole_0 = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 5.44/1.15    inference(forward_demodulation,[],[f1724,f309])).
% 5.44/1.15  fof(f1724,plain,(
% 5.44/1.15    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 5.44/1.15    inference(superposition,[],[f197,f49])).
% 5.44/1.15  fof(f197,plain,(
% 5.44/1.15    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),X0)) )),
% 5.44/1.15    inference(superposition,[],[f68,f124])).
% 5.44/1.15  fof(f4496,plain,(
% 5.44/1.15    k2_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0))),
% 5.44/1.15    inference(superposition,[],[f3749,f309])).
% 5.44/1.15  fof(f3749,plain,(
% 5.44/1.15    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0))) )),
% 5.44/1.15    inference(superposition,[],[f68,f3480])).
% 5.44/1.15  fof(f3480,plain,(
% 5.44/1.15    sK1 = k5_xboole_0(k1_xboole_0,sK1)),
% 5.44/1.15    inference(forward_demodulation,[],[f3479,f1547])).
% 5.44/1.15  fof(f1547,plain,(
% 5.44/1.15    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 5.44/1.15    inference(forward_demodulation,[],[f1546,f112])).
% 5.44/1.15  fof(f1546,plain,(
% 5.44/1.15    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)),
% 5.44/1.15    inference(forward_demodulation,[],[f1534,f51])).
% 5.44/1.15  fof(f1534,plain,(
% 5.44/1.15    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)),
% 5.44/1.15    inference(superposition,[],[f1517,f50])).
% 5.44/1.15  fof(f3479,plain,(
% 5.44/1.15    k5_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,k1_xboole_0)),
% 5.44/1.15    inference(forward_demodulation,[],[f3451,f49])).
% 5.44/1.15  fof(f3451,plain,(
% 5.44/1.15    k5_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK0,sK0))),
% 5.44/1.15    inference(superposition,[],[f2056,f120])).
% 5.44/1.15  fof(f2056,plain,(
% 5.44/1.15    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k5_xboole_0(X0,sK0))) )),
% 5.44/1.15    inference(forward_demodulation,[],[f2055,f1517])).
% 5.44/1.15  fof(f2055,plain,(
% 5.44/1.15    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK1,X0),sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X0,sK0)))) )),
% 5.44/1.15    inference(forward_demodulation,[],[f2043,f68])).
% 5.44/1.15  fof(f2043,plain,(
% 5.44/1.15    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,X0),sK0)) = k5_xboole_0(k4_xboole_0(sK1,X0),sK1)) )),
% 5.44/1.15    inference(superposition,[],[f1624,f1517])).
% 5.44/1.15  fof(f1624,plain,(
% 5.44/1.15    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k5_xboole_0(k3_xboole_0(sK1,X1),sK1)) )),
% 5.44/1.15    inference(superposition,[],[f131,f51])).
% 5.44/1.15  fof(f131,plain,(
% 5.44/1.15    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0))) )),
% 5.44/1.15    inference(forward_demodulation,[],[f128,f51])).
% 5.44/1.15  fof(f128,plain,(
% 5.44/1.15    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1)) )),
% 5.44/1.15    inference(superposition,[],[f69,f112])).
% 5.44/1.15  % SZS output end Proof for theBenchmark
% 5.44/1.15  % (28055)------------------------------
% 5.44/1.15  % (28055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.44/1.15  % (28055)Termination reason: Refutation
% 5.44/1.15  
% 5.44/1.15  % (28055)Memory used [KB]: 5628
% 5.44/1.15  % (28055)Time elapsed: 0.665 s
% 5.44/1.15  % (28055)------------------------------
% 5.44/1.15  % (28055)------------------------------
% 5.44/1.15  % (28027)Success in time 0.783 s
%------------------------------------------------------------------------------
