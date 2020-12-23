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
% DateTime   : Thu Dec  3 12:46:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  80 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 189 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f151,f164])).

fof(f164,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f159,f32])).

fof(f32,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f159,plain,
    ( sQ4_eqProxy(k1_xboole_0,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f155,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f27,f31])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f137,f43])).

fof(f43,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f137,plain,
    ( ! [X2,X3] :
        ( ~ sQ4_eqProxy(sK0,X3)
        | ~ r2_hidden(X2,X3) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_1
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,X3)
        | ~ sQ4_eqProxy(sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f151,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f43,f25,f33,f140,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X1,X3)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ r1_xboole_0(X0,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f140,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(X0,X1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_2
  <=> ! [X1,X0] : ~ r1_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f33,plain,(
    ! [X0] : sQ4_eqProxy(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f26,f31])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f141,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f134,f139,f136])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ sQ4_eqProxy(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f132,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k1_xboole_0,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f29,f34])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ sQ4_eqProxy(k1_xboole_0,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X3)
      | ~ sQ4_eqProxy(sK0,X3) ) ),
    inference(resolution,[],[f113,f23])).

fof(f23,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_setfam_1(X5,X4)
      | ~ r1_xboole_0(X2,X3)
      | ~ sQ4_eqProxy(X4,k3_xboole_0(X2,X3))
      | ~ r2_hidden(X0,X1)
      | ~ sQ4_eqProxy(X5,X1) ) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_setfam_1(X1,X3)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ r1_setfam_1(X0,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_setfam_1(X1,k3_xboole_0(X2,X3))
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f30,f29])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK3(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).

fof(f21,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK3(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (1931)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.45  % (1931)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f141,f151,f164])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    ~spl5_1),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    $false | ~spl5_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f159,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.45    inference(equality_proxy_replacement,[],[f24,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.45    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    k1_xboole_0 != sK0),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.21/0.45  fof(f159,plain,(
% 0.21/0.45    sQ4_eqProxy(k1_xboole_0,sK0) | ~spl5_1),
% 0.21/0.45    inference(resolution,[],[f155,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK1(X0),X0) | sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.45    inference(equality_proxy_replacement,[],[f27,f31])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl5_1),
% 0.21/0.45    inference(resolution,[],[f137,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.21/0.45    inference(equality_proxy_axiom,[],[f31])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~sQ4_eqProxy(sK0,X3) | ~r2_hidden(X2,X3)) ) | ~spl5_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f136])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    spl5_1 <=> ! [X3,X2] : (~r2_hidden(X2,X3) | ~sQ4_eqProxy(sK0,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.45  fof(f151,plain,(
% 0.21/0.45    ~spl5_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    $false | ~spl5_2),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f43,f25,f33,f140,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X1,X3) | ~sQ4_eqProxy(X2,X3) | ~r1_xboole_0(X0,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.45    inference(equality_proxy_axiom,[],[f31])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1)) ) | ~spl5_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f139])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    spl5_2 <=> ! [X1,X0] : ~r1_xboole_0(X0,X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0] : (sQ4_eqProxy(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.45    inference(equality_proxy_replacement,[],[f26,f31])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    spl5_1 | spl5_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f134,f139,f136])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X3) | ~sQ4_eqProxy(sK0,X3)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f132,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0,X1] : (sQ4_eqProxy(k1_xboole_0,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(resolution,[],[f29,f34])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | ~sQ4_eqProxy(k1_xboole_0,k3_xboole_0(X0,X1)) | ~r2_hidden(X2,X3) | ~sQ4_eqProxy(sK0,X3)) )),
% 0.21/0.45    inference(resolution,[],[f113,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_setfam_1(X5,X4) | ~r1_xboole_0(X2,X3) | ~sQ4_eqProxy(X4,k3_xboole_0(X2,X3)) | ~r2_hidden(X0,X1) | ~sQ4_eqProxy(X5,X1)) )),
% 0.21/0.45    inference(resolution,[],[f60,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_setfam_1(X1,X3) | ~sQ4_eqProxy(X2,X3) | ~r1_setfam_1(X0,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.45    inference(equality_proxy_axiom,[],[f31])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_setfam_1(X1,k3_xboole_0(X2,X3)) | ~r2_hidden(X0,X1) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.45    inference(resolution,[],[f30,f29])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK3(X1),X1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.46    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (1931)------------------------------
% 0.21/0.46  % (1931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (1931)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (1931)Memory used [KB]: 6140
% 0.21/0.46  % (1931)Time elapsed: 0.016 s
% 0.21/0.46  % (1931)------------------------------
% 0.21/0.46  % (1931)------------------------------
% 0.21/0.46  % (1924)Success in time 0.1 s
%------------------------------------------------------------------------------
