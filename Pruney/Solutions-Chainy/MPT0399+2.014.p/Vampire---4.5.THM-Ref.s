%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  50 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 (  99 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f71,f78])).

fof(f78,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f74,f24])).

fof(f24,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f74,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK2(k1_xboole_0),X0),k1_xboole_0)
    | ~ spl5_2 ),
    inference(resolution,[],[f63,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f63,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_2
  <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f68,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f25,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f44,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f23,f37])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f68,plain,
    ( v1_xboole_0(sK0)
    | spl5_1 ),
    inference(resolution,[],[f65,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f65,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl5_1 ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f35_D])).

fof(f35_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ r2_hidden(X2,X0)
    <=> ~ sP3(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f59,plain,
    ( ~ sP3(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_1
  <=> sP3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f64,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f49,f61,f57])).

fof(f49,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ sP3(sK0) ),
    inference(resolution,[],[f22,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X1),X1)
      | ~ sP3(X0) ) ),
    inference(general_splitting,[],[f28,f35_D])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f22,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (2111)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.50  % (2127)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.50  % (2098)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (2111)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.51  % (2119)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f64,f71,f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ~spl5_2),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    $false | ~spl5_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f74,f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK2(k1_xboole_0),X0),k1_xboole_0)) ) | ~spl5_2),
% 0.19/0.51    inference(resolution,[],[f63,f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~spl5_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f61])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    spl5_2 <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    spl5_1),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f70])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    $false | spl5_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f68,f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ~v1_xboole_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f44,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.19/0.51    inference(equality_proxy_replacement,[],[f25,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.19/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.19/0.51    inference(equality_proxy_replacement,[],[f23,f37])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    k1_xboole_0 != sK0),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.51    inference(negated_conjecture,[],[f12])).
% 0.19/0.51  fof(f12,conjecture,(
% 0.19/0.51    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    v1_xboole_0(sK0) | spl5_1),
% 0.19/0.51    inference(resolution,[],[f65,f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.19/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl5_1),
% 0.19/0.51    inference(resolution,[],[f59,f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | sP3(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f35_D])).
% 0.19/0.51  fof(f35_D,plain,(
% 0.19/0.51    ( ! [X0] : (( ! [X2] : ~r2_hidden(X2,X0) ) <=> ~sP3(X0)) )),
% 0.19/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ~sP3(sK0) | spl5_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f57])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    spl5_1 <=> sP3(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ~spl5_1 | spl5_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f49,f61,f57])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~sP3(sK0)),
% 0.19/0.51    inference(resolution,[],[f22,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | r2_hidden(sK2(X1),X1) | ~sP3(X0)) )),
% 0.19/0.51    inference(general_splitting,[],[f28,f35_D])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK2(X1),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.19/0.51    inference(unused_predicate_definition_removal,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    r1_setfam_1(sK0,k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (2111)------------------------------
% 0.19/0.51  % (2111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2111)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (2111)Memory used [KB]: 6140
% 0.19/0.51  % (2111)Time elapsed: 0.096 s
% 0.19/0.51  % (2111)------------------------------
% 0.19/0.51  % (2111)------------------------------
% 0.19/0.51  % (2096)Success in time 0.159 s
%------------------------------------------------------------------------------
