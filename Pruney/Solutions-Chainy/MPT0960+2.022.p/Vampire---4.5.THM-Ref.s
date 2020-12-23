%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:09 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 100 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   26
%              Number of atoms          :  162 ( 224 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f619,plain,(
    $false ),
    inference(subsumption_resolution,[],[f616,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f616,plain,(
    ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(resolution,[],[f607,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f17,f24,f23,f22,f21])).

fof(f21,plain,(
    ! [X3,X2,X1] :
      ( sP0(X3,X2,X1)
    <=> ( r2_hidden(k4_tarski(X2,X3),X1)
      <=> r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ! [X2,X3] :
          ( sP0(X3,X2,X1)
          | ~ r2_hidden(X3,X0)
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( sP1(X1,X0)
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( k1_wellord2(X0) = X1
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f607,plain,(
    ~ sP3(k1_wellord2(sK4),sK4) ),
    inference(subsumption_resolution,[],[f604,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f604,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK4),k2_zfmisc_1(sK4,sK4))
    | ~ sP3(k1_wellord2(sK4),sK4) ),
    inference(resolution,[],[f603,f67])).

fof(f67,plain,(
    ! [X1] :
      ( sP2(X1,k1_wellord2(X1))
      | ~ sP3(k1_wellord2(X1),X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k1_wellord2(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k1_wellord2(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f603,plain,(
    ! [X0] :
      ( ~ sP2(X0,k1_wellord2(sK4))
      | ~ r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(sK4,sK4)) ) ),
    inference(superposition,[],[f598,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f598,plain,(
    ~ r1_tarski(k2_zfmisc_1(k3_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4)) ),
    inference(subsumption_resolution,[],[f594,f41])).

fof(f594,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k3_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(superposition,[],[f560,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f560,plain,(
    ! [X1] : ~ r1_tarski(k2_zfmisc_1(k2_xboole_0(k1_relat_1(k1_wellord2(sK4)),X1),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4)) ),
    inference(superposition,[],[f510,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f510,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),X0),k2_zfmisc_1(sK4,sK4)) ),
    inference(resolution,[],[f509,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f509,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4)) ),
    inference(subsumption_resolution,[],[f507,f41])).

fof(f507,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(superposition,[],[f501,f43])).

fof(f501,plain,(
    ! [X1] : ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k2_xboole_0(X1,k2_relat_1(k1_wellord2(sK4)))),k2_zfmisc_1(sK4,sK4)) ),
    inference(superposition,[],[f256,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f256,plain,(
    ! [X16] : ~ r1_tarski(k2_xboole_0(X16,k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k2_relat_1(k1_wellord2(sK4)))),k2_zfmisc_1(sK4,sK4)) ),
    inference(subsumption_resolution,[],[f254,f41])).

fof(f254,plain,(
    ! [X16] :
      ( ~ r1_tarski(k2_xboole_0(X16,k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k2_relat_1(k1_wellord2(sK4)))),k2_zfmisc_1(sK4,sK4))
      | ~ v1_relat_1(k1_wellord2(sK4)) ) ),
    inference(resolution,[],[f244,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_wellord2(sK4),X0)
      | ~ r1_tarski(k2_xboole_0(X1,X0),k2_zfmisc_1(sK4,sK4)) ) ),
    inference(superposition,[],[f235,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f235,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_xboole_0(X0,k2_xboole_0(k1_wellord2(sK4),X1)),k2_zfmisc_1(sK4,sK4)) ),
    inference(resolution,[],[f182,f70])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k2_xboole_0(X0,k2_xboole_0(k1_wellord2(sK4),X1)),X2) ) ),
    inference(superposition,[],[f149,f59])).

fof(f149,plain,(
    ! [X17,X18,X16] : ~ r1_tarski(k2_xboole_0(k2_xboole_0(X16,k2_xboole_0(k1_wellord2(sK4),X17)),X18),k2_zfmisc_1(sK4,sK4)) ),
    inference(resolution,[],[f106,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f106,plain,(
    ! [X14,X15,X13] :
      ( ~ r1_tarski(k1_wellord2(sK4),X14)
      | ~ r1_tarski(k2_xboole_0(k2_xboole_0(X13,X14),X15),k2_zfmisc_1(sK4,sK4)) ) ),
    inference(resolution,[],[f82,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_wellord2(sK4),X0)
      | ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(sK4,sK4)) ) ),
    inference(resolution,[],[f79,f66])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X0) ) ),
    inference(superposition,[],[f71,f59])).

fof(f71,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k1_wellord2(sK4),X0),k2_zfmisc_1(sK4,sK4)) ),
    inference(resolution,[],[f40,f66])).

fof(f40,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f26])).

fof(f26,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24704)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (24700)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (24702)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (24713)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (24701)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (24701)Refutation not found, incomplete strategy% (24701)------------------------------
% 0.21/0.52  % (24701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24701)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24701)Memory used [KB]: 10618
% 0.21/0.52  % (24701)Time elapsed: 0.099 s
% 0.21/0.52  % (24701)------------------------------
% 0.21/0.52  % (24701)------------------------------
% 0.21/0.53  % (24723)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (24706)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (24705)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (24711)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (24705)Refutation not found, incomplete strategy% (24705)------------------------------
% 0.21/0.53  % (24705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24705)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24705)Memory used [KB]: 6140
% 0.21/0.53  % (24705)Time elapsed: 0.112 s
% 0.21/0.53  % (24705)------------------------------
% 0.21/0.53  % (24705)------------------------------
% 0.21/0.53  % (24706)Refutation not found, incomplete strategy% (24706)------------------------------
% 0.21/0.53  % (24706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24706)Memory used [KB]: 10490
% 0.21/0.53  % (24706)Time elapsed: 0.113 s
% 0.21/0.53  % (24706)------------------------------
% 0.21/0.53  % (24706)------------------------------
% 0.21/0.53  % (24710)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (24715)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (24721)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (24717)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (24716)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.33/0.54  % (24722)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.33/0.54  % (24709)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.33/0.54  % (24703)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.33/0.54  % (24707)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.33/0.54  % (24714)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.33/0.54  % (24708)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.33/0.54  % (24720)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.33/0.55  % (24726)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.33/0.55  % (24712)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.49/0.56  % (24719)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.49/0.56  % (24718)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.49/0.56  % (24725)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.49/0.59  % (24708)Refutation found. Thanks to Tanya!
% 1.49/0.59  % SZS status Theorem for theBenchmark
% 1.49/0.59  % SZS output start Proof for theBenchmark
% 1.49/0.59  fof(f619,plain,(
% 1.49/0.59    $false),
% 1.49/0.59    inference(subsumption_resolution,[],[f616,f41])).
% 1.49/0.59  fof(f41,plain,(
% 1.49/0.59    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f10])).
% 1.49/0.59  fof(f10,axiom,(
% 1.49/0.59    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.49/0.59  fof(f616,plain,(
% 1.49/0.59    ~v1_relat_1(k1_wellord2(sK4))),
% 1.49/0.59    inference(resolution,[],[f607,f58])).
% 1.49/0.59  fof(f58,plain,(
% 1.49/0.59    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f25])).
% 1.49/0.59  fof(f25,plain,(
% 1.49/0.59    ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1))),
% 1.49/0.59    inference(definition_folding,[],[f17,f24,f23,f22,f21])).
% 1.49/0.59  fof(f21,plain,(
% 1.49/0.59    ! [X3,X2,X1] : (sP0(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 1.49/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.49/0.59  fof(f22,plain,(
% 1.49/0.59    ! [X1,X0] : (sP1(X1,X0) <=> ! [X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 1.49/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.49/0.59  fof(f23,plain,(
% 1.49/0.59    ! [X0,X1] : (sP2(X0,X1) <=> (sP1(X1,X0) & k3_relat_1(X1) = X0))),
% 1.49/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.49/0.59  fof(f24,plain,(
% 1.49/0.59    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 1.49/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.49/0.59  fof(f17,plain,(
% 1.49/0.59    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.49/0.59    inference(flattening,[],[f16])).
% 1.49/0.59  fof(f16,plain,(
% 1.49/0.59    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f9])).
% 1.49/0.59  fof(f9,axiom,(
% 1.49/0.59    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 1.49/0.59  fof(f607,plain,(
% 1.49/0.59    ~sP3(k1_wellord2(sK4),sK4)),
% 1.49/0.59    inference(subsumption_resolution,[],[f604,f70])).
% 1.49/0.59  fof(f70,plain,(
% 1.49/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.59    inference(equality_resolution,[],[f60])).
% 1.49/0.59  fof(f60,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.49/0.59    inference(cnf_transformation,[],[f39])).
% 1.49/0.59  fof(f39,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(flattening,[],[f38])).
% 1.49/0.59  fof(f38,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(nnf_transformation,[],[f1])).
% 1.49/0.59  fof(f1,axiom,(
% 1.49/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.59  fof(f604,plain,(
% 1.49/0.59    ~r1_tarski(k2_zfmisc_1(sK4,sK4),k2_zfmisc_1(sK4,sK4)) | ~sP3(k1_wellord2(sK4),sK4)),
% 1.49/0.59    inference(resolution,[],[f603,f67])).
% 1.49/0.59  fof(f67,plain,(
% 1.49/0.59    ( ! [X1] : (sP2(X1,k1_wellord2(X1)) | ~sP3(k1_wellord2(X1),X1)) )),
% 1.49/0.59    inference(equality_resolution,[],[f45])).
% 1.49/0.59  fof(f45,plain,(
% 1.49/0.59    ( ! [X0,X1] : (sP2(X1,X0) | k1_wellord2(X1) != X0 | ~sP3(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f29])).
% 1.49/0.59  fof(f29,plain,(
% 1.49/0.59    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k1_wellord2(X1) != X0)) | ~sP3(X0,X1))),
% 1.49/0.59    inference(rectify,[],[f28])).
% 1.49/0.59  fof(f28,plain,(
% 1.49/0.59    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_wellord2(X0) != X1)) | ~sP3(X1,X0))),
% 1.49/0.59    inference(nnf_transformation,[],[f24])).
% 1.49/0.59  fof(f603,plain,(
% 1.49/0.59    ( ! [X0] : (~sP2(X0,k1_wellord2(sK4)) | ~r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(superposition,[],[f598,f47])).
% 1.49/0.59  fof(f47,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | ~sP2(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f31])).
% 1.49/0.59  fof(f31,plain,(
% 1.49/0.59    ! [X0,X1] : ((sP2(X0,X1) | ~sP1(X1,X0) | k3_relat_1(X1) != X0) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 1.49/0.59    inference(flattening,[],[f30])).
% 1.49/0.59  fof(f30,plain,(
% 1.49/0.59    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0) | k3_relat_1(X1) != X0)) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 1.49/0.59    inference(nnf_transformation,[],[f23])).
% 1.49/0.59  fof(f598,plain,(
% 1.49/0.59    ~r1_tarski(k2_zfmisc_1(k3_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4))),
% 1.49/0.59    inference(subsumption_resolution,[],[f594,f41])).
% 1.49/0.59  fof(f594,plain,(
% 1.49/0.59    ~r1_tarski(k2_zfmisc_1(k3_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4)) | ~v1_relat_1(k1_wellord2(sK4))),
% 1.49/0.59    inference(superposition,[],[f560,f43])).
% 1.49/0.59  fof(f43,plain,(
% 1.49/0.59    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f15])).
% 1.49/0.59  fof(f15,plain,(
% 1.49/0.59    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f7])).
% 1.49/0.59  fof(f7,axiom,(
% 1.49/0.59    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.49/0.59  fof(f560,plain,(
% 1.49/0.59    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(k2_xboole_0(k1_relat_1(k1_wellord2(sK4)),X1),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(superposition,[],[f510,f63])).
% 1.49/0.59  fof(f63,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f6])).
% 1.49/0.59  fof(f6,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.49/0.59  fof(f510,plain,(
% 1.49/0.59    ( ! [X0] : (~r1_tarski(k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),X0),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(resolution,[],[f509,f66])).
% 1.49/0.59  fof(f66,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f20])).
% 1.49/0.59  fof(f20,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.49/0.59    inference(ennf_transformation,[],[f3])).
% 1.49/0.59  fof(f3,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.49/0.59  fof(f509,plain,(
% 1.49/0.59    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4))),
% 1.49/0.59    inference(subsumption_resolution,[],[f507,f41])).
% 1.49/0.59  fof(f507,plain,(
% 1.49/0.59    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k3_relat_1(k1_wellord2(sK4))),k2_zfmisc_1(sK4,sK4)) | ~v1_relat_1(k1_wellord2(sK4))),
% 1.49/0.59    inference(superposition,[],[f501,f43])).
% 1.49/0.59  fof(f501,plain,(
% 1.49/0.59    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k2_xboole_0(X1,k2_relat_1(k1_wellord2(sK4)))),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(superposition,[],[f256,f64])).
% 1.49/0.59  fof(f64,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f6])).
% 1.49/0.59  fof(f256,plain,(
% 1.49/0.59    ( ! [X16] : (~r1_tarski(k2_xboole_0(X16,k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k2_relat_1(k1_wellord2(sK4)))),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f254,f41])).
% 1.49/0.59  fof(f254,plain,(
% 1.49/0.59    ( ! [X16] : (~r1_tarski(k2_xboole_0(X16,k2_zfmisc_1(k1_relat_1(k1_wellord2(sK4)),k2_relat_1(k1_wellord2(sK4)))),k2_zfmisc_1(sK4,sK4)) | ~v1_relat_1(k1_wellord2(sK4))) )),
% 1.49/0.59    inference(resolution,[],[f244,f42])).
% 1.49/0.59  fof(f42,plain,(
% 1.49/0.59    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f14])).
% 1.49/0.59  fof(f14,plain,(
% 1.49/0.59    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f8])).
% 1.49/0.59  fof(f8,axiom,(
% 1.49/0.59    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.49/0.59  fof(f244,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tarski(k1_wellord2(sK4),X0) | ~r1_tarski(k2_xboole_0(X1,X0),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(superposition,[],[f235,f59])).
% 1.49/0.59  fof(f59,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f18])).
% 1.49/0.59  fof(f18,plain,(
% 1.49/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f4])).
% 1.49/0.59  fof(f4,axiom,(
% 1.49/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.49/0.59  fof(f235,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X0,k2_xboole_0(k1_wellord2(sK4),X1)),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(resolution,[],[f182,f70])).
% 1.49/0.59  fof(f182,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k2_xboole_0(X0,k2_xboole_0(k1_wellord2(sK4),X1)),X2)) )),
% 1.49/0.59    inference(superposition,[],[f149,f59])).
% 1.49/0.59  fof(f149,plain,(
% 1.49/0.59    ( ! [X17,X18,X16] : (~r1_tarski(k2_xboole_0(k2_xboole_0(X16,k2_xboole_0(k1_wellord2(sK4),X17)),X18),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(resolution,[],[f106,f44])).
% 1.49/0.59  fof(f44,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f5])).
% 1.49/0.59  fof(f5,axiom,(
% 1.49/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.49/0.59  fof(f106,plain,(
% 1.49/0.59    ( ! [X14,X15,X13] : (~r1_tarski(k1_wellord2(sK4),X14) | ~r1_tarski(k2_xboole_0(k2_xboole_0(X13,X14),X15),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(resolution,[],[f82,f65])).
% 1.49/0.59  fof(f65,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f19])).
% 1.49/0.59  fof(f19,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f2])).
% 1.49/0.59  fof(f2,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.49/0.59  fof(f82,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tarski(k1_wellord2(sK4),X0) | ~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(resolution,[],[f79,f66])).
% 1.49/0.59  fof(f79,plain,(
% 1.49/0.59    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k1_wellord2(sK4),X0)) )),
% 1.49/0.59    inference(superposition,[],[f71,f59])).
% 1.49/0.59  fof(f71,plain,(
% 1.49/0.59    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_wellord2(sK4),X0),k2_zfmisc_1(sK4,sK4))) )),
% 1.49/0.59    inference(resolution,[],[f40,f66])).
% 1.49/0.59  fof(f40,plain,(
% 1.49/0.59    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 1.49/0.59    inference(cnf_transformation,[],[f27])).
% 1.49/0.59  fof(f27,plain,(
% 1.49/0.59    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 1.49/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f26])).
% 1.49/0.59  fof(f26,plain,(
% 1.49/0.59    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f13,plain,(
% 1.49/0.59    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f12])).
% 1.49/0.59  fof(f12,negated_conjecture,(
% 1.49/0.59    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.49/0.59    inference(negated_conjecture,[],[f11])).
% 1.49/0.59  fof(f11,conjecture,(
% 1.49/0.59    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 1.49/0.59  % SZS output end Proof for theBenchmark
% 1.49/0.59  % (24708)------------------------------
% 1.49/0.59  % (24708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (24708)Termination reason: Refutation
% 1.49/0.59  
% 1.49/0.59  % (24708)Memory used [KB]: 1918
% 1.49/0.59  % (24708)Time elapsed: 0.164 s
% 1.49/0.59  % (24708)------------------------------
% 1.49/0.59  % (24708)------------------------------
% 1.49/0.59  % (24699)Success in time 0.226 s
%------------------------------------------------------------------------------
