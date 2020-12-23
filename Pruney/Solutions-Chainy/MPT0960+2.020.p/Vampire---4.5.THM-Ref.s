%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 127 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 ( 348 expanded)
%              Number of equality atoms :   27 (  58 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f194,f200,f262])).

fof(f262,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f258,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl7_6 ),
    inference(resolution,[],[f257,f72])).

fof(f72,plain,(
    ! [X0] : sP2(X0,k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f71,plain,(
    ! [X0] :
      ( sP2(X0,k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f16,f24,f23,f22,f21])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f66,plain,(
    ! [X1] :
      ( ~ sP3(k1_wellord2(X1),X1)
      | sP2(X1,k1_wellord2(X1)) ) ),
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

fof(f257,plain,
    ( ! [X0] :
        ( ~ sP2(X0,k1_wellord2(sK4))
        | ~ r1_tarski(X0,sK4) )
    | spl7_6 ),
    inference(superposition,[],[f254,f47])).

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

% (16765)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (16764)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f254,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f253,f41])).

fof(f253,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4))
    | spl7_6 ),
    inference(superposition,[],[f243,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f243,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k2_relat_1(k1_wellord2(sK4))),sK4)
    | spl7_6 ),
    inference(resolution,[],[f219,f68])).

fof(f219,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),X4)
        | ~ r1_tarski(k2_xboole_0(X3,X4),sK4) )
    | spl7_6 ),
    inference(resolution,[],[f212,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl7_6 ),
    inference(resolution,[],[f193,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f193,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl7_6
  <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f200,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f198,f72])).

fof(f198,plain,
    ( ~ sP2(sK4,k1_wellord2(sK4))
    | spl7_5 ),
    inference(subsumption_resolution,[],[f195,f41])).

fof(f195,plain,
    ( ~ v1_relat_1(k1_wellord2(sK4))
    | ~ sP2(sK4,k1_wellord2(sK4))
    | spl7_5 ),
    inference(resolution,[],[f189,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ sP2(X1,X0) ) ),
    inference(superposition,[],[f91,f47])).

fof(f91,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f189,plain,
    ( ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_5
  <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f194,plain,
    ( ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f185,f191,f187])).

fof(f185,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) ),
    inference(subsumption_resolution,[],[f182,f41])).

fof(f182,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(resolution,[],[f173,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f173,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(X17,X16))
      | ~ r1_tarski(X16,sK4)
      | ~ r1_tarski(X17,sK4) ) ),
    inference(resolution,[],[f64,f153])).

fof(f153,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X14,k2_zfmisc_1(X13,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X14)
      | ~ r1_tarski(X13,sK4) ) ),
    inference(resolution,[],[f63,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X0) ) ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f26])).

fof(f26,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

% (16777)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (16766)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (16766)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (16783)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (16775)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (16767)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.21/0.51  % (16767)Refutation not found, incomplete strategy% (16767)------------------------------
% 1.21/0.51  % (16767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.51  % (16767)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.51  
% 1.21/0.51  % (16767)Memory used [KB]: 6140
% 1.21/0.51  % (16767)Time elapsed: 0.091 s
% 1.21/0.51  % (16767)------------------------------
% 1.21/0.51  % (16767)------------------------------
% 1.21/0.51  % SZS output start Proof for theBenchmark
% 1.21/0.51  fof(f263,plain,(
% 1.21/0.51    $false),
% 1.21/0.51    inference(avatar_sat_refutation,[],[f194,f200,f262])).
% 1.21/0.51  fof(f262,plain,(
% 1.21/0.51    spl7_6),
% 1.21/0.51    inference(avatar_contradiction_clause,[],[f261])).
% 1.21/0.51  fof(f261,plain,(
% 1.21/0.51    $false | spl7_6),
% 1.21/0.51    inference(subsumption_resolution,[],[f258,f68])).
% 1.21/0.51  fof(f68,plain,(
% 1.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.21/0.51    inference(equality_resolution,[],[f60])).
% 1.21/0.51  fof(f60,plain,(
% 1.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.21/0.51    inference(cnf_transformation,[],[f39])).
% 1.21/0.51  fof(f39,plain,(
% 1.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.21/0.51    inference(flattening,[],[f38])).
% 1.21/0.51  fof(f38,plain,(
% 1.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.21/0.51    inference(nnf_transformation,[],[f1])).
% 1.21/0.51  fof(f1,axiom,(
% 1.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.21/0.51  fof(f258,plain,(
% 1.21/0.51    ~r1_tarski(sK4,sK4) | spl7_6),
% 1.21/0.51    inference(resolution,[],[f257,f72])).
% 1.21/0.51  fof(f72,plain,(
% 1.21/0.51    ( ! [X0] : (sP2(X0,k1_wellord2(X0))) )),
% 1.21/0.51    inference(subsumption_resolution,[],[f71,f41])).
% 1.21/0.51  fof(f41,plain,(
% 1.21/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.21/0.51    inference(cnf_transformation,[],[f9])).
% 1.21/0.51  fof(f9,axiom,(
% 1.21/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.21/0.51  fof(f71,plain,(
% 1.21/0.51    ( ! [X0] : (sP2(X0,k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.21/0.51    inference(resolution,[],[f66,f58])).
% 1.21/0.51  fof(f58,plain,(
% 1.21/0.51    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f25])).
% 1.21/0.51  fof(f25,plain,(
% 1.21/0.51    ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1))),
% 1.21/0.51    inference(definition_folding,[],[f16,f24,f23,f22,f21])).
% 1.21/0.51  fof(f21,plain,(
% 1.21/0.51    ! [X3,X2,X1] : (sP0(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 1.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.21/0.51  fof(f22,plain,(
% 1.21/0.51    ! [X1,X0] : (sP1(X1,X0) <=> ! [X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 1.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.21/0.51  fof(f23,plain,(
% 1.21/0.51    ! [X0,X1] : (sP2(X0,X1) <=> (sP1(X1,X0) & k3_relat_1(X1) = X0))),
% 1.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.21/0.51  fof(f24,plain,(
% 1.21/0.51    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 1.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.21/0.51  fof(f16,plain,(
% 1.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.21/0.51    inference(flattening,[],[f15])).
% 1.21/0.51  fof(f15,plain,(
% 1.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.21/0.51    inference(ennf_transformation,[],[f8])).
% 1.21/0.51  fof(f8,axiom,(
% 1.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 1.21/0.51  fof(f66,plain,(
% 1.21/0.51    ( ! [X1] : (~sP3(k1_wellord2(X1),X1) | sP2(X1,k1_wellord2(X1))) )),
% 1.21/0.51    inference(equality_resolution,[],[f45])).
% 1.21/0.51  fof(f45,plain,(
% 1.21/0.51    ( ! [X0,X1] : (sP2(X1,X0) | k1_wellord2(X1) != X0 | ~sP3(X0,X1)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f29])).
% 1.21/0.51  fof(f29,plain,(
% 1.21/0.51    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k1_wellord2(X1) != X0)) | ~sP3(X0,X1))),
% 1.21/0.51    inference(rectify,[],[f28])).
% 1.21/0.51  fof(f28,plain,(
% 1.21/0.51    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_wellord2(X0) != X1)) | ~sP3(X1,X0))),
% 1.21/0.51    inference(nnf_transformation,[],[f24])).
% 1.21/0.51  fof(f257,plain,(
% 1.21/0.51    ( ! [X0] : (~sP2(X0,k1_wellord2(sK4)) | ~r1_tarski(X0,sK4)) ) | spl7_6),
% 1.21/0.51    inference(superposition,[],[f254,f47])).
% 1.21/0.51  fof(f47,plain,(
% 1.21/0.51    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | ~sP2(X0,X1)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f31])).
% 1.21/0.51  fof(f31,plain,(
% 1.21/0.51    ! [X0,X1] : ((sP2(X0,X1) | ~sP1(X1,X0) | k3_relat_1(X1) != X0) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 1.21/0.51    inference(flattening,[],[f30])).
% 1.21/0.51  fof(f30,plain,(
% 1.21/0.51    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0) | k3_relat_1(X1) != X0)) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 1.21/0.51    inference(nnf_transformation,[],[f23])).
% 1.21/0.51  % (16765)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.21/0.51  % (16764)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.21/0.51  fof(f254,plain,(
% 1.21/0.51    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | spl7_6),
% 1.21/0.51    inference(subsumption_resolution,[],[f253,f41])).
% 1.21/0.51  fof(f253,plain,(
% 1.21/0.51    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4)) | spl7_6),
% 1.21/0.51    inference(superposition,[],[f243,f43])).
% 1.21/0.51  fof(f43,plain,(
% 1.21/0.51    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f14])).
% 1.21/0.51  fof(f14,plain,(
% 1.21/0.51    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.21/0.51    inference(ennf_transformation,[],[f6])).
% 1.21/0.51  fof(f6,axiom,(
% 1.21/0.51    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.21/0.51  fof(f243,plain,(
% 1.21/0.51    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k2_relat_1(k1_wellord2(sK4))),sK4)) ) | spl7_6),
% 1.21/0.51    inference(resolution,[],[f219,f68])).
% 1.21/0.51  fof(f219,plain,(
% 1.21/0.51    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(k1_wellord2(sK4)),X4) | ~r1_tarski(k2_xboole_0(X3,X4),sK4)) ) | spl7_6),
% 1.21/0.51    inference(resolution,[],[f212,f62])).
% 1.21/0.51  fof(f62,plain,(
% 1.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f17])).
% 1.21/0.51  fof(f17,plain,(
% 1.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.21/0.51    inference(ennf_transformation,[],[f2])).
% 1.21/0.51  fof(f2,axiom,(
% 1.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.21/0.51  fof(f212,plain,(
% 1.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_wellord2(sK4)),X0) | ~r1_tarski(X0,sK4)) ) | spl7_6),
% 1.21/0.51    inference(resolution,[],[f193,f65])).
% 1.21/0.51  fof(f65,plain,(
% 1.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f20])).
% 1.21/0.51  fof(f20,plain,(
% 1.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.21/0.51    inference(flattening,[],[f19])).
% 1.21/0.51  fof(f19,plain,(
% 1.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.21/0.51    inference(ennf_transformation,[],[f3])).
% 1.21/0.51  fof(f3,axiom,(
% 1.21/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.21/0.51  fof(f193,plain,(
% 1.21/0.51    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | spl7_6),
% 1.21/0.51    inference(avatar_component_clause,[],[f191])).
% 1.21/0.51  fof(f191,plain,(
% 1.21/0.51    spl7_6 <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)),
% 1.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.21/0.51  fof(f200,plain,(
% 1.21/0.51    spl7_5),
% 1.21/0.51    inference(avatar_contradiction_clause,[],[f199])).
% 1.21/0.51  fof(f199,plain,(
% 1.21/0.51    $false | spl7_5),
% 1.21/0.51    inference(subsumption_resolution,[],[f198,f72])).
% 1.21/0.51  fof(f198,plain,(
% 1.21/0.51    ~sP2(sK4,k1_wellord2(sK4)) | spl7_5),
% 1.21/0.51    inference(subsumption_resolution,[],[f195,f41])).
% 1.21/0.51  fof(f195,plain,(
% 1.21/0.51    ~v1_relat_1(k1_wellord2(sK4)) | ~sP2(sK4,k1_wellord2(sK4)) | spl7_5),
% 1.21/0.51    inference(resolution,[],[f189,f93])).
% 1.21/0.51  fof(f93,plain,(
% 1.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~sP2(X1,X0)) )),
% 1.21/0.51    inference(superposition,[],[f91,f47])).
% 1.21/0.51  fof(f91,plain,(
% 1.21/0.51    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.21/0.51    inference(superposition,[],[f44,f43])).
% 1.21/0.51  fof(f44,plain,(
% 1.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.21/0.51    inference(cnf_transformation,[],[f4])).
% 1.21/0.51  fof(f4,axiom,(
% 1.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.21/0.51  fof(f189,plain,(
% 1.21/0.51    ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | spl7_5),
% 1.21/0.51    inference(avatar_component_clause,[],[f187])).
% 1.21/0.51  fof(f187,plain,(
% 1.21/0.51    spl7_5 <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)),
% 1.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.21/0.51  fof(f194,plain,(
% 1.21/0.51    ~spl7_5 | ~spl7_6),
% 1.21/0.51    inference(avatar_split_clause,[],[f185,f191,f187])).
% 1.21/0.51  fof(f185,plain,(
% 1.21/0.51    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)),
% 1.21/0.51    inference(subsumption_resolution,[],[f182,f41])).
% 1.21/0.51  fof(f182,plain,(
% 1.21/0.51    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4))),
% 1.21/0.51    inference(resolution,[],[f173,f42])).
% 1.21/0.51  fof(f42,plain,(
% 1.21/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f13])).
% 1.21/0.51  fof(f13,plain,(
% 1.21/0.51    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.21/0.51    inference(ennf_transformation,[],[f7])).
% 1.21/0.51  fof(f7,axiom,(
% 1.21/0.51    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.21/0.51  fof(f173,plain,(
% 1.21/0.51    ( ! [X17,X16] : (~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(X17,X16)) | ~r1_tarski(X16,sK4) | ~r1_tarski(X17,sK4)) )),
% 1.21/0.51    inference(resolution,[],[f64,f153])).
% 1.21/0.51  fof(f153,plain,(
% 1.21/0.51    ( ! [X14,X13] : (~r1_tarski(X14,k2_zfmisc_1(X13,sK4)) | ~r1_tarski(k1_wellord2(sK4),X14) | ~r1_tarski(X13,sK4)) )),
% 1.21/0.51    inference(resolution,[],[f63,f83])).
% 1.21/0.51  fof(f83,plain,(
% 1.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k1_wellord2(sK4),X0) | ~r1_tarski(X0,X1)) )),
% 1.21/0.51    inference(resolution,[],[f80,f65])).
% 1.21/0.51  fof(f80,plain,(
% 1.21/0.51    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k1_wellord2(sK4),X0)) )),
% 1.21/0.51    inference(resolution,[],[f65,f40])).
% 1.21/0.51  fof(f40,plain,(
% 1.21/0.51    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 1.21/0.51    inference(cnf_transformation,[],[f27])).
% 1.21/0.51  fof(f27,plain,(
% 1.21/0.51    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 1.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f26])).
% 1.21/0.51  fof(f26,plain,(
% 1.21/0.51    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 1.21/0.51    introduced(choice_axiom,[])).
% 1.21/0.51  fof(f12,plain,(
% 1.21/0.51    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.21/0.51    inference(ennf_transformation,[],[f11])).
% 1.21/0.51  fof(f11,negated_conjecture,(
% 1.21/0.51    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.21/0.51    inference(negated_conjecture,[],[f10])).
% 1.21/0.51  fof(f10,conjecture,(
% 1.21/0.51    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
% 1.21/0.51  fof(f63,plain,(
% 1.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.21/0.51    inference(cnf_transformation,[],[f18])).
% 1.21/0.51  fof(f18,plain,(
% 1.21/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.21/0.51    inference(ennf_transformation,[],[f5])).
% 1.21/0.51  fof(f5,axiom,(
% 1.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.21/0.52  % (16777)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.21/0.52  fof(f64,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f18])).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (16766)------------------------------
% 1.21/0.52  % (16766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (16766)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (16766)Memory used [KB]: 6268
% 1.21/0.52  % (16766)Time elapsed: 0.093 s
% 1.21/0.52  % (16766)------------------------------
% 1.21/0.52  % (16766)------------------------------
% 1.21/0.52  % (16761)Success in time 0.155 s
%------------------------------------------------------------------------------
