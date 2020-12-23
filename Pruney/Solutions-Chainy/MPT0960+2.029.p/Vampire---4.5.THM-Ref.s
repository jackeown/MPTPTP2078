%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 149 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  217 ( 438 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f180,f223])).

fof(f223,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f219,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f219,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl8_4 ),
    inference(resolution,[],[f218,f75])).

fof(f75,plain,(
    ! [X0] : sP2(X0,k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f74,plain,(
    ! [X0] :
      ( sP2(X0,k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f16,f25,f24,f23,f22])).

fof(f22,plain,(
    ! [X3,X2,X1] :
      ( sP0(X3,X2,X1)
    <=> ( r2_hidden(k4_tarski(X2,X3),X1)
      <=> r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ! [X2,X3] :
          ( sP0(X3,X2,X1)
          | ~ r2_hidden(X3,X0)
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( sP1(X1,X0)
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f69,plain,(
    ! [X1] :
      ( ~ sP3(k1_wellord2(X1),X1)
      | sP2(X1,k1_wellord2(X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k1_wellord2(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k1_wellord2(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ sP2(X0,k1_wellord2(sK4))
        | ~ r1_tarski(X0,sK4) )
    | spl8_4 ),
    inference(superposition,[],[f215,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f215,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f214,f44])).

fof(f214,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4))
    | spl8_4 ),
    inference(superposition,[],[f206,f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f206,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k2_relat_1(k1_wellord2(sK4))),sK4)
    | spl8_4 ),
    inference(resolution,[],[f187,f73])).

fof(f187,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),X4)
        | ~ r1_tarski(k2_xboole_0(X3,X4),sK4) )
    | spl8_4 ),
    inference(resolution,[],[f182,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl8_4 ),
    inference(resolution,[],[f173,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f173,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_4
  <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f180,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f178,f75])).

fof(f178,plain,
    ( ~ sP2(sK4,k1_wellord2(sK4))
    | spl8_3 ),
    inference(subsumption_resolution,[],[f175,f44])).

fof(f175,plain,
    ( ~ v1_relat_1(k1_wellord2(sK4))
    | ~ sP2(sK4,k1_wellord2(sK4))
    | spl8_3 ),
    inference(resolution,[],[f169,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ sP2(X1,X0) ) ),
    inference(superposition,[],[f88,f50])).

fof(f88,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

% (31811)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f169,plain,
    ( ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_3
  <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f174,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f165,f171,f167])).

fof(f165,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f162,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(resolution,[],[f154,f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f154,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(X17,X16))
      | ~ r1_tarski(X16,sK4)
      | ~ r1_tarski(X17,sK4) ) ),
    inference(resolution,[],[f67,f137])).

fof(f137,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X14,k2_zfmisc_1(X13,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X14)
      | ~ r1_tarski(X13,sK4) ) ),
    inference(resolution,[],[f66,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f80,f68])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X0) ) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f27])).

fof(f27,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31808)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (31816)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (31818)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (31810)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (31825)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (31805)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (31815)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (31829)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (31820)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (31832)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (31804)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (31812)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (31820)Refutation not found, incomplete strategy% (31820)------------------------------
% 0.22/0.54  % (31820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31817)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (31803)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (31820)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31820)Memory used [KB]: 10618
% 0.22/0.54  % (31820)Time elapsed: 0.128 s
% 0.22/0.54  % (31820)------------------------------
% 0.22/0.54  % (31820)------------------------------
% 0.22/0.54  % (31813)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (31806)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (31807)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (31826)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (31809)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (31830)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (31819)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (31821)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (31827)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (31830)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f174,f180,f223])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    spl8_4),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f222])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    $false | spl8_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f219,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f64,f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    ~r1_tarski(sK4,sK4) | spl8_4),
% 0.22/0.55    inference(resolution,[],[f218,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0] : (sP2(X0,k1_wellord2(X0))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f74,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X0] : (sP2(X0,k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.55    inference(resolution,[],[f69,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(definition_folding,[],[f16,f25,f24,f23,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X3,X2,X1] : (sP0(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X1,X0] : (sP1(X1,X0) <=> ! [X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1] : (sP2(X0,X1) <=> (sP1(X1,X0) & k3_relat_1(X1) = X0))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X1] : (~sP3(k1_wellord2(X1),X1) | sP2(X1,k1_wellord2(X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sP2(X1,X0) | k1_wellord2(X1) != X0 | ~sP3(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k1_wellord2(X1) != X0)) | ~sP3(X0,X1))),
% 0.22/0.55    inference(rectify,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_wellord2(X0) != X1)) | ~sP3(X1,X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f25])).
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    ( ! [X0] : (~sP2(X0,k1_wellord2(sK4)) | ~r1_tarski(X0,sK4)) ) | spl8_4),
% 0.22/0.55    inference(superposition,[],[f215,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | ~sP2(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : ((sP2(X0,X1) | ~sP1(X1,X0) | k3_relat_1(X1) != X0) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.22/0.55    inference(flattening,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0) | k3_relat_1(X1) != X0)) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f24])).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | spl8_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f214,f44])).
% 0.22/0.55  fof(f214,plain,(
% 0.22/0.55    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4)) | spl8_4),
% 0.22/0.55    inference(superposition,[],[f206,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k2_relat_1(k1_wellord2(sK4))),sK4)) ) | spl8_4),
% 0.22/0.55    inference(resolution,[],[f187,f73])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(k1_wellord2(sK4)),X4) | ~r1_tarski(k2_xboole_0(X3,X4),sK4)) ) | spl8_4),
% 0.22/0.55    inference(resolution,[],[f182,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_wellord2(sK4)),X0) | ~r1_tarski(X0,sK4)) ) | spl8_4),
% 0.22/0.55    inference(resolution,[],[f173,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | spl8_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f171])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    spl8_4 <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    spl8_3),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f179])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    $false | spl8_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f178,f75])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    ~sP2(sK4,k1_wellord2(sK4)) | spl8_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f175,f44])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    ~v1_relat_1(k1_wellord2(sK4)) | ~sP2(sK4,k1_wellord2(sK4)) | spl8_3),
% 0.22/0.55    inference(resolution,[],[f169,f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~sP2(X1,X0)) )),
% 0.22/0.55    inference(superposition,[],[f88,f50])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(superposition,[],[f47,f46])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  % (31811)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | spl8_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f167])).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    spl8_3 <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    ~spl8_3 | ~spl8_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f165,f171,f167])).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f162,f44])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4))),
% 0.22/0.55    inference(resolution,[],[f154,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(X17,X16)) | ~r1_tarski(X16,sK4) | ~r1_tarski(X17,sK4)) )),
% 0.22/0.55    inference(resolution,[],[f67,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    ( ! [X14,X13] : (~r1_tarski(X14,k2_zfmisc_1(X13,sK4)) | ~r1_tarski(k1_wellord2(sK4),X14) | ~r1_tarski(X13,sK4)) )),
% 0.22/0.55    inference(resolution,[],[f66,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k1_wellord2(sK4),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f80,f68])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k1_wellord2(sK4),X0)) )),
% 0.22/0.55    inference(resolution,[],[f68,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,negated_conjecture,(
% 0.22/0.55    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.55    inference(negated_conjecture,[],[f10])).
% 0.22/0.55  fof(f10,conjecture,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (31830)------------------------------
% 0.22/0.55  % (31830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31830)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (31830)Memory used [KB]: 6268
% 0.22/0.55  % (31830)Time elapsed: 0.142 s
% 0.22/0.55  % (31830)------------------------------
% 0.22/0.55  % (31830)------------------------------
% 0.22/0.55  % (31824)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (31811)Refutation not found, incomplete strategy% (31811)------------------------------
% 0.22/0.55  % (31811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31811)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31811)Memory used [KB]: 10618
% 0.22/0.55  % (31811)Time elapsed: 0.148 s
% 0.22/0.55  % (31811)------------------------------
% 0.22/0.55  % (31811)------------------------------
% 0.22/0.55  % (31823)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (31828)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (31822)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (31802)Success in time 0.196 s
%------------------------------------------------------------------------------
