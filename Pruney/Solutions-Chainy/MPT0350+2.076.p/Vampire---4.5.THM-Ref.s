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
% DateTime   : Thu Dec  3 12:44:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 720 expanded)
%              Number of leaves         :   21 ( 223 expanded)
%              Depth                    :   20
%              Number of atoms          :  206 (1421 expanded)
%              Number of equality atoms :   76 ( 625 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f516,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f358,f515])).

fof(f515,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f513])).

% (9746)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f513,plain,
    ( sK0 != sK0
    | ~ spl3_10 ),
    inference(superposition,[],[f342,f508])).

fof(f508,plain,
    ( sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f502,f341])).

fof(f341,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f338,f340])).

fof(f340,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f75,f331])).

fof(f331,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f236,f297])).

fof(f297,plain,(
    sK1 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k1_xboole_0)) ),
    inference(superposition,[],[f108,f106])).

fof(f106,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f105,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f105,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f58,f103])).

fof(f103,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(resolution,[],[f97,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f83,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_tarski(k1_enumset1(X2,X2,X3)) = X3 ) ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f20])).

% (9747)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(resolution,[],[f61,f65])).

fof(f65,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f39,f43,f57])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f108,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[],[f60,f38])).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f44,f57,f43])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f236,plain,(
    ! [X4] : k3_tarski(k1_enumset1(X4,X4,k1_xboole_0)) = X4 ),
    inference(superposition,[],[f68,f161])).

fof(f161,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f135,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f135,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(resolution,[],[f101,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f101,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = X1 ) ),
    inference(resolution,[],[f97,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f50,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f76,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f58,f59])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f62,f67])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[],[f59,f38])).

fof(f75,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f62,f33])).

fof(f338,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f114,f331])).

fof(f114,plain,(
    sK0 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f60,f75])).

fof(f502,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_10 ),
    inference(resolution,[],[f361,f33])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(sK0,sK1))) )
    | ~ spl3_10 ),
    inference(resolution,[],[f357,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f357,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl3_10
  <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f342,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f66,f340])).

fof(f66,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f34,f36])).

fof(f34,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f358,plain,
    ( ~ spl3_1
    | spl3_10 ),
    inference(avatar_split_clause,[],[f353,f355,f147])).

fof(f147,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f353,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f50,f340])).

fof(f158,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f149,f33])).

fof(f149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (9749)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9759)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (9757)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (9751)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (9757)Refutation not found, incomplete strategy% (9757)------------------------------
% 0.21/0.51  % (9757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9759)Refutation not found, incomplete strategy% (9759)------------------------------
% 0.21/0.51  % (9759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9743)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (9759)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9759)Memory used [KB]: 10746
% 0.21/0.51  % (9759)Time elapsed: 0.061 s
% 0.21/0.51  % (9759)------------------------------
% 0.21/0.51  % (9759)------------------------------
% 0.21/0.52  % (9765)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (9748)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (9757)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9757)Memory used [KB]: 10746
% 0.21/0.52  % (9757)Time elapsed: 0.105 s
% 0.21/0.52  % (9757)------------------------------
% 0.21/0.52  % (9757)------------------------------
% 0.21/0.53  % (9737)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (9741)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (9766)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (9739)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (9738)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (9749)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (9742)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f516,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f158,f358,f515])).
% 0.21/0.54  fof(f515,plain,(
% 0.21/0.54    ~spl3_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f514])).
% 0.21/0.54  fof(f514,plain,(
% 0.21/0.54    $false | ~spl3_10),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f513])).
% 0.21/0.54  % (9746)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  fof(f513,plain,(
% 0.21/0.54    sK0 != sK0 | ~spl3_10),
% 0.21/0.54    inference(superposition,[],[f342,f508])).
% 0.21/0.54  fof(f508,plain,(
% 0.21/0.54    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | ~spl3_10),
% 0.21/0.54    inference(forward_demodulation,[],[f502,f341])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.54    inference(backward_demodulation,[],[f338,f340])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f75,f331])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(superposition,[],[f236,f297])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    sK1 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k1_xboole_0))),
% 0.21/0.54    inference(superposition,[],[f108,f106])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(forward_demodulation,[],[f105,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),
% 0.21/0.54    inference(superposition,[],[f58,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    sK0 = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 0.21/0.54    inference(resolution,[],[f97,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f17])).
% 0.21/0.54  fof(f17,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 0.21/0.54    inference(resolution,[],[f83,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X3] : (v1_xboole_0(k1_zfmisc_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k1_enumset1(X2,X2,X3)) = X3) )),
% 0.21/0.54    inference(resolution,[],[f72,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  % (9747)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 0.21/0.54    inference(resolution,[],[f61,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f49,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f41,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f39,f43,f57])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0) )),
% 0.21/0.54    inference(superposition,[],[f60,f38])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f44,f57,f43])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ( ! [X4] : (k3_tarski(k1_enumset1(X4,X4,k1_xboole_0)) = X4) )),
% 0.21/0.54    inference(superposition,[],[f68,f161])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(superposition,[],[f135,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f40,f57])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 0.21/0.54    inference(resolution,[],[f101,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f37,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = X1) )),
% 0.21/0.54    inference(resolution,[],[f97,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(superposition,[],[f50,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f76,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 0.21/0.54    inference(superposition,[],[f58,f59])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f62,f67])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f51,f43])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0) )),
% 0.21/0.54    inference(superposition,[],[f59,f38])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f62,f33])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 0.21/0.54    inference(backward_demodulation,[],[f114,f331])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    sK0 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)))),
% 0.21/0.54    inference(superposition,[],[f60,f75])).
% 0.21/0.54  fof(f502,plain,(
% 0.21/0.54    k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | ~spl3_10),
% 0.21/0.54    inference(resolution,[],[f361,f33])).
% 0.21/0.55  fof(f361,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(sK0,sK1)))) ) | ~spl3_10),
% 0.21/0.55    inference(resolution,[],[f357,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f56,f57])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.55  fof(f357,plain,(
% 0.21/0.55    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f355])).
% 0.21/0.55  fof(f355,plain,(
% 0.21/0.55    spl3_10 <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.55  fof(f342,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f66,f340])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f34,f36])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f358,plain,(
% 0.21/0.55    ~spl3_1 | spl3_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f353,f355,f147])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f353,plain,(
% 0.21/0.55    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(superposition,[],[f50,f340])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    spl3_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    $false | spl3_1),
% 0.21/0.55    inference(resolution,[],[f149,f33])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f147])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (9749)------------------------------
% 0.21/0.55  % (9749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9749)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (9749)Memory used [KB]: 6524
% 0.21/0.55  % (9749)Time elapsed: 0.130 s
% 0.21/0.55  % (9749)------------------------------
% 0.21/0.55  % (9749)------------------------------
% 0.21/0.55  % (9752)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (9752)Refutation not found, incomplete strategy% (9752)------------------------------
% 0.21/0.55  % (9752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9752)Memory used [KB]: 6140
% 0.21/0.55  % (9752)Time elapsed: 0.002 s
% 0.21/0.55  % (9752)------------------------------
% 0.21/0.55  % (9752)------------------------------
% 0.21/0.55  % (9736)Success in time 0.188 s
%------------------------------------------------------------------------------
