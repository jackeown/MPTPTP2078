%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:37 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 228 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   23
%              Number of atoms          :  200 ( 799 expanded)
%              Number of equality atoms :   48 ( 234 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(subsumption_resolution,[],[f239,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f31,plain,
    ( sK2 != k1_subset_1(sK1)
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( sK2 != k1_subset_1(sK1)
      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & ( sK2 = k1_subset_1(sK1)
      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK2 != k1_subset_1(sK1)
        | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & ( sK2 = k1_subset_1(sK1)
        | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f239,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f238,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f238,plain,(
    ~ r2_hidden(sK3(sK2),sK2) ),
    inference(resolution,[],[f235,f47])).

fof(f47,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f15])).

% (12492)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f15,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f235,plain,(
    ! [X4,X3] :
      ( ~ sP0(X3,X4,k4_xboole_0(sK1,sK2))
      | ~ r2_hidden(sK3(sK2),X3) ) ),
    inference(resolution,[],[f232,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f232,plain,(
    r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f231,f65])).

fof(f65,plain,(
    sP0(k5_xboole_0(sK2,sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f59,f64])).

fof(f64,plain,(
    k4_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f36,f54])).

fof(f54,plain,(
    sK2 = k3_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f48,f51])).

fof(f48,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f30,f33])).

fof(f30,plain,
    ( sK2 = k1_subset_1(sK1)
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

% (12491)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    sP0(k4_xboole_0(sK2,k3_subset_1(sK1,sK2)),sK2,sK2) ),
    inference(superposition,[],[f56,f54])).

fof(f56,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f231,plain,(
    ! [X0] :
      ( ~ sP0(k5_xboole_0(sK2,sK2),X0,sK2)
      | r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f227,f51])).

fof(f227,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2))
      | ~ sP0(k5_xboole_0(sK2,sK2),X0,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f226,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0),X1)
      | ~ sP0(X1,X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f34])).

fof(f226,plain,
    ( r2_hidden(sK3(sK2),k5_xboole_0(sK2,sK2))
    | r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f224,f51])).

fof(f224,plain,
    ( r2_hidden(sK3(sK2),k5_xboole_0(sK2,sK2))
    | r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f179,f111])).

fof(f111,plain,(
    sP0(k4_xboole_0(sK1,sK2),sK2,k5_xboole_0(sK2,sK2)) ),
    inference(backward_demodulation,[],[f101,f110])).

% (12495)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f110,plain,(
    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f101,plain,(
    sP0(k3_subset_1(sK1,sK2),sK2,k5_xboole_0(sK2,sK2)) ),
    inference(superposition,[],[f47,f64])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | r2_hidden(sK3(X0),X2)
      | r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f41,f34])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (12493)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (12485)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (12485)Refutation not found, incomplete strategy% (12485)------------------------------
% 0.22/0.56  % (12485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12485)Memory used [KB]: 6140
% 0.22/0.56  % (12485)Time elapsed: 0.003 s
% 0.22/0.56  % (12485)------------------------------
% 0.22/0.56  % (12485)------------------------------
% 0.22/0.56  % (12477)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (12482)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.57  % (12477)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % (12498)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.57  % (12470)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f240,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(subsumption_resolution,[],[f239,f51])).
% 1.57/0.57  fof(f51,plain,(
% 1.57/0.57    k1_xboole_0 != sK2),
% 1.57/0.57    inference(subsumption_resolution,[],[f50,f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    k1_xboole_0 != sK2 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0))),
% 1.57/0.57    inference(inner_rewriting,[],[f49])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    k1_xboole_0 != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.57/0.57    inference(backward_demodulation,[],[f31,f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    sK2 != k1_subset_1(sK1) | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    (sK2 != k1_subset_1(sK1) | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (sK2 = k1_subset_1(sK1) | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK2 != k1_subset_1(sK1) | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (sK2 = k1_subset_1(sK1) | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(flattening,[],[f17])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(nnf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,plain,(
% 1.57/0.57    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.57/0.57    inference(negated_conjecture,[],[f9])).
% 1.57/0.57  fof(f9,conjecture,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 1.57/0.57  fof(f239,plain,(
% 1.57/0.57    k1_xboole_0 = sK2),
% 1.57/0.57    inference(resolution,[],[f238,f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f12,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.57/0.57    inference(ennf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.57/0.57  fof(f238,plain,(
% 1.57/0.57    ~r2_hidden(sK3(sK2),sK2)),
% 1.57/0.57    inference(resolution,[],[f235,f47])).
% 1.57/0.57  fof(f47,plain,(
% 1.57/0.57    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(equality_resolution,[],[f45])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.57    inference(nnf_transformation,[],[f16])).
% 1.57/0.57  fof(f16,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.57/0.57    inference(definition_folding,[],[f1,f15])).
% 1.57/0.57  % (12492)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.57  fof(f15,plain,(
% 1.57/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.57/0.57  fof(f235,plain,(
% 1.57/0.57    ( ! [X4,X3] : (~sP0(X3,X4,k4_xboole_0(sK1,sK2)) | ~r2_hidden(sK3(sK2),X3)) )),
% 1.57/0.57    inference(resolution,[],[f232,f40])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.57/0.57    inference(rectify,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.57/0.57    inference(flattening,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.57/0.57    inference(nnf_transformation,[],[f15])).
% 1.57/0.57  fof(f232,plain,(
% 1.57/0.57    r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2))),
% 1.57/0.57    inference(resolution,[],[f231,f65])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    sP0(k5_xboole_0(sK2,sK2),sK2,sK2)),
% 1.57/0.57    inference(backward_demodulation,[],[f59,f64])).
% 1.57/0.57  fof(f64,plain,(
% 1.57/0.57    k4_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k5_xboole_0(sK2,sK2)),
% 1.57/0.57    inference(superposition,[],[f36,f54])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    sK2 = k3_xboole_0(sK2,k3_subset_1(sK1,sK2))),
% 1.57/0.57    inference(resolution,[],[f37,f52])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.57/0.57    inference(subsumption_resolution,[],[f48,f51])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.57/0.57    inference(backward_demodulation,[],[f30,f33])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    sK2 = k1_subset_1(sK1) | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f13])).
% 1.57/0.57  % (12491)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.57  fof(f13,plain,(
% 1.57/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    sP0(k4_xboole_0(sK2,k3_subset_1(sK1,sK2)),sK2,sK2)),
% 1.57/0.57    inference(superposition,[],[f56,f54])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    ( ! [X0,X1] : (sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(superposition,[],[f47,f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.57  fof(f231,plain,(
% 1.57/0.57    ( ! [X0] : (~sP0(k5_xboole_0(sK2,sK2),X0,sK2) | r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2))) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f227,f51])).
% 1.57/0.57  fof(f227,plain,(
% 1.57/0.57    ( ! [X0] : (r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2)) | ~sP0(k5_xboole_0(sK2,sK2),X0,sK2) | k1_xboole_0 = sK2) )),
% 1.57/0.57    inference(resolution,[],[f226,f109])).
% 1.57/0.57  fof(f109,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0),X1) | ~sP0(X1,X2,X0) | k1_xboole_0 = X0) )),
% 1.57/0.57    inference(resolution,[],[f40,f34])).
% 1.57/0.57  fof(f226,plain,(
% 1.57/0.57    r2_hidden(sK3(sK2),k5_xboole_0(sK2,sK2)) | r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2))),
% 1.57/0.57    inference(subsumption_resolution,[],[f224,f51])).
% 1.57/0.57  fof(f224,plain,(
% 1.57/0.57    r2_hidden(sK3(sK2),k5_xboole_0(sK2,sK2)) | r2_hidden(sK3(sK2),k4_xboole_0(sK1,sK2)) | k1_xboole_0 = sK2),
% 1.57/0.57    inference(resolution,[],[f179,f111])).
% 1.57/0.57  fof(f111,plain,(
% 1.57/0.57    sP0(k4_xboole_0(sK1,sK2),sK2,k5_xboole_0(sK2,sK2))),
% 1.57/0.57    inference(backward_demodulation,[],[f101,f110])).
% 1.57/0.57  % (12495)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.57/0.57  fof(f110,plain,(
% 1.57/0.57    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 1.57/0.57    inference(resolution,[],[f38,f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,plain,(
% 1.57/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.57/0.57  fof(f101,plain,(
% 1.57/0.57    sP0(k3_subset_1(sK1,sK2),sK2,k5_xboole_0(sK2,sK2))),
% 1.57/0.57    inference(superposition,[],[f47,f64])).
% 1.57/0.57  fof(f179,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | r2_hidden(sK3(X0),X2) | r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 1.57/0.57    inference(resolution,[],[f41,f34])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f27])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (12477)------------------------------
% 1.57/0.57  % (12477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (12477)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (12477)Memory used [KB]: 6396
% 1.57/0.57  % (12477)Time elapsed: 0.081 s
% 1.57/0.57  % (12477)------------------------------
% 1.57/0.57  % (12477)------------------------------
% 1.57/0.57  % (12492)Refutation not found, incomplete strategy% (12492)------------------------------
% 1.57/0.57  % (12492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (12492)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (12492)Memory used [KB]: 10618
% 1.57/0.57  % (12492)Time elapsed: 0.132 s
% 1.57/0.57  % (12492)------------------------------
% 1.57/0.57  % (12492)------------------------------
% 1.57/0.57  % (12497)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.58  % (12469)Success in time 0.203 s
%------------------------------------------------------------------------------
