%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:20 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 142 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   22
%              Number of atoms          :  202 ( 594 expanded)
%              Number of equality atoms :   40 ( 105 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f158])).

fof(f158,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f28,f150])).

fof(f150,plain,(
    sK1 = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f143,f58])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK2))) ),
    inference(superposition,[],[f57,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK2,sK1))
    & r1_tarski(sK1,k1_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK1 != k1_relat_1(k7_relat_1(sK2,sK1))
      & r1_tarski(sK1,k1_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f143,plain,(
    sK1 = k1_setfam_1(k2_tarski(sK1,k1_relat_1(sK2))) ),
    inference(resolution,[],[f129,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (30816)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f129,plain,(
    sP0(k1_relat_1(sK2),sK1,sK1) ),
    inference(resolution,[],[f126,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f126,plain,(
    ~ r2_hidden(sK4(k1_relat_1(sK2),sK1,sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK4(k1_relat_1(sK2),sK1,sK1),sK1) ),
    inference(superposition,[],[f28,f122])).

fof(f122,plain,(
    ! [X0] :
      ( k1_relat_1(k7_relat_1(sK2,X0)) = X0
      | ~ r2_hidden(sK4(k1_relat_1(sK2),X0,X0),sK1) ) ),
    inference(forward_demodulation,[],[f120,f58])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k1_relat_1(sK2),X0,X0),sK1)
      | k1_setfam_1(k2_tarski(X0,k1_relat_1(sK2))) = X0 ) ),
    inference(resolution,[],[f106,f27])).

fof(f27,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f106,plain,(
    ! [X17,X18,X16] :
      ( ~ r1_tarski(X18,X17)
      | ~ r2_hidden(sK4(X17,X16,X16),X18)
      | k1_setfam_1(k2_tarski(X16,X17)) = X16 ) ),
    inference(resolution,[],[f98,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1
      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ) ),
    inference(resolution,[],[f91,f44])).

fof(f91,plain,(
    ! [X4,X5] :
      ( sP0(X5,X4,X4)
      | ~ r2_hidden(sK4(X5,X4,X4),X5)
      | k1_setfam_1(k2_tarski(X4,X5)) = X4 ) ),
    inference(resolution,[],[f88,f76])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1
      | ~ r2_hidden(sK4(X0,X1,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1
      | ~ r2_hidden(sK4(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ) ),
    inference(resolution,[],[f81,f44])).

fof(f81,plain,(
    ! [X6,X7] :
      ( sP0(X6,X7,X7)
      | ~ r2_hidden(sK4(X6,X7,X7),X6)
      | k1_setfam_1(k2_tarski(X7,X6)) = X7
      | ~ r2_hidden(sK4(X6,X7,X7),X7) ) ),
    inference(resolution,[],[f78,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X2 ) ),
    inference(resolution,[],[f40,f44])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f28,plain,(
    sK1 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (30815)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (30827)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (30825)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.21/0.52  % (30819)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.53  % (30807)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.53  % (30823)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.21/0.53  % (30806)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.53  % (30827)Refutation not found, incomplete strategy% (30827)------------------------------
% 1.21/0.53  % (30827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (30827)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (30827)Memory used [KB]: 10618
% 1.21/0.53  % (30827)Time elapsed: 0.078 s
% 1.21/0.53  % (30827)------------------------------
% 1.21/0.53  % (30827)------------------------------
% 1.21/0.53  % (30815)Refutation not found, incomplete strategy% (30815)------------------------------
% 1.21/0.53  % (30815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (30815)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (30815)Memory used [KB]: 10618
% 1.21/0.53  % (30815)Time elapsed: 0.115 s
% 1.21/0.53  % (30815)------------------------------
% 1.21/0.53  % (30815)------------------------------
% 1.21/0.53  % (30828)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.53  % (30821)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.21/0.53  % (30805)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.53  % (30817)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.53  % (30808)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.53  % (30809)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.53  % (30809)Refutation not found, incomplete strategy% (30809)------------------------------
% 1.21/0.53  % (30809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (30809)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (30809)Memory used [KB]: 6140
% 1.21/0.53  % (30809)Time elapsed: 0.121 s
% 1.21/0.53  % (30809)------------------------------
% 1.21/0.53  % (30809)------------------------------
% 1.21/0.53  % (30812)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.53  % (30817)Refutation found. Thanks to Tanya!
% 1.21/0.53  % SZS status Theorem for theBenchmark
% 1.21/0.53  % SZS output start Proof for theBenchmark
% 1.21/0.53  fof(f161,plain,(
% 1.21/0.53    $false),
% 1.21/0.53    inference(trivial_inequality_removal,[],[f158])).
% 1.21/0.53  fof(f158,plain,(
% 1.21/0.53    sK1 != sK1),
% 1.21/0.53    inference(superposition,[],[f28,f150])).
% 1.21/0.53  fof(f150,plain,(
% 1.21/0.53    sK1 = k1_relat_1(k7_relat_1(sK2,sK1))),
% 1.21/0.53    inference(superposition,[],[f143,f58])).
% 1.21/0.53  fof(f58,plain,(
% 1.21/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK2)))) )),
% 1.21/0.53    inference(superposition,[],[f57,f29])).
% 1.21/0.53  fof(f29,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f3])).
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.21/0.53  fof(f57,plain,(
% 1.21/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0))) )),
% 1.21/0.53    inference(resolution,[],[f43,f26])).
% 1.21/0.53  fof(f26,plain,(
% 1.21/0.53    v1_relat_1(sK2)),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f15,plain,(
% 1.21/0.53    sK1 != k1_relat_1(k7_relat_1(sK2,sK1)) & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2)),
% 1.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f14])).
% 1.21/0.53  fof(f14,plain,(
% 1.21/0.53    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (sK1 != k1_relat_1(k7_relat_1(sK2,sK1)) & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2))),
% 1.21/0.53    introduced(choice_axiom,[])).
% 1.21/0.53  fof(f9,plain,(
% 1.21/0.53    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.21/0.53    inference(flattening,[],[f8])).
% 1.21/0.53  fof(f8,plain,(
% 1.21/0.53    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,negated_conjecture,(
% 1.21/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.21/0.53    inference(negated_conjecture,[],[f6])).
% 1.21/0.53  fof(f6,conjecture,(
% 1.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.21/0.53  fof(f43,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.21/0.53    inference(definition_unfolding,[],[f31,f30])).
% 1.21/0.53  fof(f30,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f4])).
% 1.21/0.53  fof(f4,axiom,(
% 1.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.21/0.53  fof(f31,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,plain,(
% 1.21/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f5])).
% 1.21/0.53  fof(f5,axiom,(
% 1.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.21/0.53  fof(f143,plain,(
% 1.21/0.53    sK1 = k1_setfam_1(k2_tarski(sK1,k1_relat_1(sK2)))),
% 1.21/0.53    inference(resolution,[],[f129,f44])).
% 1.21/0.53  fof(f44,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.21/0.53    inference(definition_unfolding,[],[f42,f30])).
% 1.21/0.53  fof(f42,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f25])).
% 1.21/0.53  fof(f25,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.21/0.53    inference(nnf_transformation,[],[f13])).
% 1.21/0.53  fof(f13,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.21/0.53    inference(definition_folding,[],[f2,f12])).
% 1.21/0.53  fof(f12,plain,(
% 1.21/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.21/0.53  % (30816)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.21/0.53  fof(f129,plain,(
% 1.21/0.53    sP0(k1_relat_1(sK2),sK1,sK1)),
% 1.21/0.53    inference(resolution,[],[f126,f76])).
% 1.21/0.53  fof(f76,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.21/0.53    inference(factoring,[],[f38])).
% 1.21/0.53  fof(f38,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f24])).
% 1.21/0.53  fof(f24,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.21/0.53    introduced(choice_axiom,[])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.21/0.53    inference(rectify,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.21/0.53    inference(flattening,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.21/0.53    inference(nnf_transformation,[],[f12])).
% 1.21/0.53  fof(f126,plain,(
% 1.21/0.53    ~r2_hidden(sK4(k1_relat_1(sK2),sK1,sK1),sK1)),
% 1.21/0.53    inference(trivial_inequality_removal,[],[f123])).
% 1.21/0.53  fof(f123,plain,(
% 1.21/0.53    sK1 != sK1 | ~r2_hidden(sK4(k1_relat_1(sK2),sK1,sK1),sK1)),
% 1.21/0.53    inference(superposition,[],[f28,f122])).
% 1.21/0.53  fof(f122,plain,(
% 1.21/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = X0 | ~r2_hidden(sK4(k1_relat_1(sK2),X0,X0),sK1)) )),
% 1.21/0.53    inference(forward_demodulation,[],[f120,f58])).
% 1.21/0.53  fof(f120,plain,(
% 1.21/0.53    ( ! [X0] : (~r2_hidden(sK4(k1_relat_1(sK2),X0,X0),sK1) | k1_setfam_1(k2_tarski(X0,k1_relat_1(sK2))) = X0) )),
% 1.21/0.53    inference(resolution,[],[f106,f27])).
% 1.21/0.53  fof(f27,plain,(
% 1.21/0.53    r1_tarski(sK1,k1_relat_1(sK2))),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f106,plain,(
% 1.21/0.53    ( ! [X17,X18,X16] : (~r1_tarski(X18,X17) | ~r2_hidden(sK4(X17,X16,X16),X18) | k1_setfam_1(k2_tarski(X16,X17)) = X16) )),
% 1.21/0.53    inference(resolution,[],[f98,f32])).
% 1.21/0.53  fof(f32,plain,(
% 1.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f19])).
% 1.21/0.53  fof(f19,plain,(
% 1.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.21/0.53  fof(f18,plain,(
% 1.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.21/0.53    introduced(choice_axiom,[])).
% 1.21/0.53  fof(f17,plain,(
% 1.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.21/0.53    inference(rectify,[],[f16])).
% 1.21/0.53  fof(f16,plain,(
% 1.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.21/0.53    inference(nnf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,plain,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.21/0.53    inference(ennf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.21/0.53  fof(f98,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X1) )),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f97])).
% 1.21/0.53  fof(f97,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X1 | k1_setfam_1(k2_tarski(X1,X0)) = X1) )),
% 1.21/0.53    inference(resolution,[],[f91,f44])).
% 1.21/0.53  fof(f91,plain,(
% 1.21/0.53    ( ! [X4,X5] : (sP0(X5,X4,X4) | ~r2_hidden(sK4(X5,X4,X4),X5) | k1_setfam_1(k2_tarski(X4,X5)) = X4) )),
% 1.21/0.53    inference(resolution,[],[f88,f76])).
% 1.21/0.53  fof(f88,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X1,X0)) = X1 | ~r2_hidden(sK4(X0,X1,X1),X0)) )),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f87])).
% 1.21/0.53  fof(f87,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X1 | ~r2_hidden(sK4(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X1,X0)) = X1) )),
% 1.21/0.53    inference(resolution,[],[f81,f44])).
% 1.21/0.53  fof(f81,plain,(
% 1.21/0.53    ( ! [X6,X7] : (sP0(X6,X7,X7) | ~r2_hidden(sK4(X6,X7,X7),X6) | k1_setfam_1(k2_tarski(X7,X6)) = X7 | ~r2_hidden(sK4(X6,X7,X7),X7)) )),
% 1.21/0.53    inference(resolution,[],[f78,f76])).
% 1.21/0.53  fof(f78,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X2) )),
% 1.21/0.53    inference(resolution,[],[f40,f44])).
% 1.21/0.53  fof(f40,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f24])).
% 1.21/0.53  fof(f28,plain,(
% 1.21/0.53    sK1 != k1_relat_1(k7_relat_1(sK2,sK1))),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  % SZS output end Proof for theBenchmark
% 1.21/0.53  % (30817)------------------------------
% 1.21/0.53  % (30817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (30817)Termination reason: Refutation
% 1.21/0.53  
% 1.21/0.53  % (30817)Memory used [KB]: 6268
% 1.21/0.53  % (30817)Time elapsed: 0.133 s
% 1.21/0.53  % (30817)------------------------------
% 1.21/0.53  % (30817)------------------------------
% 1.21/0.53  % (30810)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.53  % (30830)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.21/0.53  % (30833)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.21/0.53  % (30820)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.53  % (30811)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.54  % (30829)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.21/0.54  % (30822)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.21/0.54  % (30804)Success in time 0.18 s
%------------------------------------------------------------------------------
