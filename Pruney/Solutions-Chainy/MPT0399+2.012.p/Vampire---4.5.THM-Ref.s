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
% DateTime   : Thu Dec  3 12:46:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 126 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f124,f138])).

fof(f138,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f135,f31])).

fof(f31,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f135,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f130,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sQ3_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f25,f30])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f130,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f116,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f116,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_2
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f124,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f121,f32])).

fof(f32,plain,(
    ! [X0] : sQ3_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(equality_proxy_replacement,[],[f24,f30])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f121,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0))))
    | spl4_1 ),
    inference(resolution,[],[f113,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f113,plain,
    ( ~ sQ3_eqProxy(k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0))),k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_1
  <=> sQ3_eqProxy(k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f117,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f108,f115,f111])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ sQ3_eqProxy(k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0))),k1_xboole_0) ) ),
    inference(resolution,[],[f58,f22])).

fof(f22,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ sQ3_eqProxy(k4_xboole_0(X2,k1_tarski(sK2(X2))),X2) ) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ sQ3_eqProxy(k4_xboole_0(X0,k1_tarski(X1)),X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK2(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK2(X1),X1) ) ),
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
    inference(pure_predicate_removal,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:59:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (24066)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (24074)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (24066)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f117,f124,f138])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    ~spl4_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f137])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    $false | ~spl4_2),
% 0.22/0.47    inference(subsumption_resolution,[],[f135,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ~sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f23,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    k1_xboole_0 != sK0),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    sQ3_eqProxy(k1_xboole_0,sK0) | ~spl4_2),
% 0.22/0.47    inference(resolution,[],[f130,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | sQ3_eqProxy(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f25,f30])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    v1_xboole_0(sK0) | ~spl4_2),
% 0.22/0.47    inference(resolution,[],[f116,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl4_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f115])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    spl4_2 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    spl4_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    $false | spl4_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f121,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0] : (sQ3_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f24,f30])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    ~sQ3_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0)))) | spl4_1),
% 0.22/0.47    inference(resolution,[],[f113,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f30])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~sQ3_eqProxy(k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0))),k1_xboole_0) | spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f111])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    spl4_1 <=> sQ3_eqProxy(k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0))),k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    ~spl4_1 | spl4_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f108,f115,f111])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,sK0) | ~sQ3_eqProxy(k4_xboole_0(k1_xboole_0,k1_tarski(sK2(k1_xboole_0))),k1_xboole_0)) )),
% 0.22/0.47    inference(resolution,[],[f58,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    r1_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_setfam_1(X1,X2) | ~r2_hidden(X0,X1) | ~sQ3_eqProxy(k4_xboole_0(X2,k1_tarski(sK2(X2))),X2)) )),
% 0.22/0.47    inference(resolution,[],[f27,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~sQ3_eqProxy(k4_xboole_0(X0,k1_tarski(X1)),X0)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f28,f30])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK2(X1),X1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.22/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (24066)------------------------------
% 0.22/0.47  % (24066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (24066)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (24066)Memory used [KB]: 6140
% 0.22/0.47  % (24066)Time elapsed: 0.049 s
% 0.22/0.47  % (24066)------------------------------
% 0.22/0.47  % (24066)------------------------------
% 0.22/0.48  % (24060)Success in time 0.111 s
%------------------------------------------------------------------------------
