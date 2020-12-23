%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:51 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 318 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  168 ( 870 expanded)
%              Number of equality atoms :   66 ( 257 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f697,plain,(
    $false ),
    inference(subsumption_resolution,[],[f696,f126])).

fof(f126,plain,(
    sK0 != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f87,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f86,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f83])).

fof(f83,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f77,f76])).

fof(f76,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f77,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f85,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f82,f66])).

fof(f66,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f82,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f73,f76])).

fof(f73,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f41,f43])).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f696,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f695,f296])).

fof(f296,plain,(
    sK0 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f291,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f291,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f236,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f236,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f65,f221])).

fof(f221,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f204,f160])).

fof(f160,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f156,f104])).

fof(f104,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f50,f94])).

fof(f94,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f93,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f93,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f88,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f84,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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

% (15543)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f84,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f78,f42])).

% (15530)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f78,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f156,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f96,f65])).

fof(f96,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f52,f93])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f204,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f127,f44])).

fof(f127,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f65,f104])).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f695,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f681,f45])).

fof(f681,plain,(
    k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
    inference(superposition,[],[f423,f221])).

fof(f423,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f65,f408])).

fof(f408,plain,(
    k1_xboole_0 = k5_xboole_0(k2_xboole_0(sK1,sK0),sK0) ),
    inference(superposition,[],[f158,f44])).

fof(f158,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK1,X0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[],[f65,f96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:02:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (15532)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (15552)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (15544)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (15544)Refutation not found, incomplete strategy% (15544)------------------------------
% 0.21/0.57  % (15544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (15544)Memory used [KB]: 6140
% 0.21/0.57  % (15544)Time elapsed: 0.005 s
% 0.21/0.57  % (15544)------------------------------
% 0.21/0.57  % (15544)------------------------------
% 1.49/0.57  % (15536)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.58  % (15542)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.58  % (15548)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.59  % (15556)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.74/0.59  % (15529)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.74/0.59  % (15535)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.74/0.59  % (15531)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.74/0.60  % (15534)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.74/0.60  % (15533)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.74/0.60  % (15541)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.74/0.60  % (15552)Refutation found. Thanks to Tanya!
% 1.74/0.60  % SZS status Theorem for theBenchmark
% 1.74/0.60  % SZS output start Proof for theBenchmark
% 1.74/0.60  fof(f697,plain,(
% 1.74/0.60    $false),
% 1.74/0.60    inference(subsumption_resolution,[],[f696,f126])).
% 1.74/0.60  fof(f126,plain,(
% 1.74/0.60    sK0 != k2_xboole_0(sK1,sK0)),
% 1.74/0.60    inference(superposition,[],[f87,f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f4])).
% 1.74/0.60  fof(f4,axiom,(
% 1.74/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.74/0.60  fof(f87,plain,(
% 1.74/0.60    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.74/0.60    inference(subsumption_resolution,[],[f86,f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.74/0.60    inference(cnf_transformation,[],[f34])).
% 1.74/0.60  fof(f34,plain,(
% 1.74/0.60    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f33])).
% 1.74/0.60  fof(f33,plain,(
% 1.74/0.60    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f26,plain,(
% 1.74/0.60    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f25])).
% 1.74/0.60  fof(f25,negated_conjecture,(
% 1.74/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.74/0.60    inference(negated_conjecture,[],[f24])).
% 1.74/0.60  fof(f24,conjecture,(
% 1.74/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.74/0.60  fof(f86,plain,(
% 1.74/0.60    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.74/0.60    inference(subsumption_resolution,[],[f85,f83])).
% 1.74/0.60  fof(f83,plain,(
% 1.74/0.60    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.74/0.60    inference(forward_demodulation,[],[f77,f76])).
% 1.74/0.60  fof(f76,plain,(
% 1.74/0.60    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.74/0.60    inference(resolution,[],[f40,f59])).
% 1.74/0.60  fof(f59,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f30])).
% 1.74/0.60  fof(f30,plain,(
% 1.74/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f20])).
% 1.74/0.60  fof(f20,axiom,(
% 1.74/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.74/0.60  fof(f77,plain,(
% 1.74/0.60    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.74/0.60    inference(resolution,[],[f40,f58])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f29])).
% 1.74/0.60  fof(f29,plain,(
% 1.74/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f21])).
% 1.74/0.60  fof(f21,axiom,(
% 1.74/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.74/0.60  fof(f85,plain,(
% 1.74/0.60    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.74/0.60    inference(superposition,[],[f82,f66])).
% 1.74/0.60  fof(f66,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f32])).
% 1.74/0.60  fof(f32,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.60    inference(flattening,[],[f31])).
% 1.74/0.60  fof(f31,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.74/0.60    inference(ennf_transformation,[],[f23])).
% 1.74/0.60  fof(f23,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.74/0.60  fof(f82,plain,(
% 1.74/0.60    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.74/0.60    inference(backward_demodulation,[],[f73,f76])).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.74/0.60    inference(forward_demodulation,[],[f41,f43])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f19])).
% 1.74/0.60  fof(f19,axiom,(
% 1.74/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.74/0.60    inference(cnf_transformation,[],[f34])).
% 1.74/0.60  fof(f696,plain,(
% 1.74/0.60    sK0 = k2_xboole_0(sK1,sK0)),
% 1.74/0.60    inference(forward_demodulation,[],[f695,f296])).
% 1.74/0.60  fof(f296,plain,(
% 1.74/0.60    sK0 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0))),
% 1.74/0.60    inference(forward_demodulation,[],[f291,f45])).
% 1.74/0.60  fof(f45,plain,(
% 1.74/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f5])).
% 1.74/0.60  fof(f5,axiom,(
% 1.74/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.74/0.60  fof(f291,plain,(
% 1.74/0.60    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0))),
% 1.74/0.60    inference(superposition,[],[f236,f44])).
% 1.74/0.60  fof(f44,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f7])).
% 1.74/0.60  fof(f7,axiom,(
% 1.74/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.74/0.60  fof(f236,plain,(
% 1.74/0.60    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.74/0.60    inference(superposition,[],[f65,f221])).
% 1.74/0.60  fof(f221,plain,(
% 1.74/0.60    k1_xboole_0 = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 1.74/0.60    inference(forward_demodulation,[],[f204,f160])).
% 1.74/0.60  fof(f160,plain,(
% 1.74/0.60    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.74/0.60    inference(forward_demodulation,[],[f156,f104])).
% 1.74/0.60  fof(f104,plain,(
% 1.74/0.60    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.74/0.60    inference(superposition,[],[f50,f94])).
% 1.74/0.60  fof(f94,plain,(
% 1.74/0.60    sK1 = k3_xboole_0(sK0,sK1)),
% 1.74/0.60    inference(superposition,[],[f93,f47])).
% 1.74/0.60  fof(f47,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.74/0.60  fof(f93,plain,(
% 1.74/0.60    sK1 = k3_xboole_0(sK1,sK0)),
% 1.74/0.60    inference(resolution,[],[f88,f57])).
% 1.74/0.60  fof(f57,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f28])).
% 1.74/0.60  fof(f28,plain,(
% 1.74/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f3])).
% 1.74/0.60  fof(f3,axiom,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.74/0.60  fof(f88,plain,(
% 1.74/0.60    r1_tarski(sK1,sK0)),
% 1.74/0.60    inference(resolution,[],[f84,f72])).
% 1.74/0.60  fof(f72,plain,(
% 1.74/0.60    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.74/0.60    inference(equality_resolution,[],[f60])).
% 1.74/0.60  fof(f60,plain,(
% 1.74/0.60    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f39])).
% 1.74/0.60  fof(f39,plain,(
% 1.74/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 1.74/0.60  fof(f38,plain,(
% 1.74/0.60    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f37,plain,(
% 1.74/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.74/0.60    inference(rectify,[],[f36])).
% 1.74/0.61  fof(f36,plain,(
% 1.74/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.74/0.61    inference(nnf_transformation,[],[f16])).
% 1.74/0.61  % (15543)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.74/0.61  fof(f16,axiom,(
% 1.74/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.74/0.61  fof(f84,plain,(
% 1.74/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.74/0.61    inference(subsumption_resolution,[],[f78,f42])).
% 1.74/0.61  % (15530)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.74/0.61  fof(f42,plain,(
% 1.74/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f22])).
% 1.74/0.61  fof(f22,axiom,(
% 1.74/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.74/0.61  fof(f78,plain,(
% 1.74/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.74/0.61    inference(resolution,[],[f40,f53])).
% 1.74/0.61  fof(f53,plain,(
% 1.74/0.61    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f35])).
% 1.74/0.61  fof(f35,plain,(
% 1.74/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.74/0.61    inference(nnf_transformation,[],[f27])).
% 1.74/0.61  fof(f27,plain,(
% 1.74/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f18])).
% 1.74/0.61  fof(f18,axiom,(
% 1.74/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.74/0.61  fof(f50,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f2])).
% 1.74/0.61  fof(f2,axiom,(
% 1.74/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.74/0.61  fof(f156,plain,(
% 1.74/0.61    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.74/0.61    inference(superposition,[],[f96,f65])).
% 1.74/0.61  fof(f96,plain,(
% 1.74/0.61    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 1.74/0.61    inference(superposition,[],[f52,f93])).
% 1.74/0.61  fof(f52,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f8])).
% 1.74/0.61  fof(f8,axiom,(
% 1.74/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.74/0.61  fof(f204,plain,(
% 1.74/0.61    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 1.74/0.61    inference(superposition,[],[f127,f44])).
% 1.74/0.61  fof(f127,plain,(
% 1.74/0.61    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),X0)) )),
% 1.74/0.61    inference(superposition,[],[f65,f104])).
% 1.74/0.61  fof(f65,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f6])).
% 1.74/0.61  fof(f6,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.74/0.61  fof(f695,plain,(
% 1.74/0.61    k2_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0))),
% 1.74/0.61    inference(forward_demodulation,[],[f681,f45])).
% 1.74/0.61  fof(f681,plain,(
% 1.74/0.61    k5_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0)),
% 1.74/0.61    inference(superposition,[],[f423,f221])).
% 1.74/0.61  fof(f423,plain,(
% 1.74/0.61    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,X0))) )),
% 1.74/0.61    inference(superposition,[],[f65,f408])).
% 1.74/0.61  fof(f408,plain,(
% 1.74/0.61    k1_xboole_0 = k5_xboole_0(k2_xboole_0(sK1,sK0),sK0)),
% 1.74/0.61    inference(superposition,[],[f158,f44])).
% 1.74/0.61  fof(f158,plain,(
% 1.74/0.61    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK1,X0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),X0)) )),
% 1.74/0.61    inference(superposition,[],[f65,f96])).
% 1.74/0.61  % SZS output end Proof for theBenchmark
% 1.74/0.61  % (15552)------------------------------
% 1.74/0.61  % (15552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (15552)Termination reason: Refutation
% 1.74/0.61  
% 1.74/0.61  % (15552)Memory used [KB]: 2174
% 1.74/0.61  % (15552)Time elapsed: 0.115 s
% 1.74/0.61  % (15552)------------------------------
% 1.74/0.61  % (15552)------------------------------
% 1.74/0.61  % (15528)Success in time 0.245 s
%------------------------------------------------------------------------------
