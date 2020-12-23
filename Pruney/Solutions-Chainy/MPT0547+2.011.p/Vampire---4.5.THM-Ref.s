%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 148 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f37,f56,f62,f77,f84])).

fof(f84,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl4_6 ),
    inference(resolution,[],[f52,f14])).

fof(f14,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f52,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(X0,X1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_6
  <=> ! [X1,X0] : ~ r1_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f77,plain,
    ( spl4_1
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f74,f25])).

fof(f25,plain,
    ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f74,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)
    | ~ spl4_8 ),
    inference(resolution,[],[f61,f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f61,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_8
  <=> ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f62,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f58,f54,f35,f60])).

fof(f35,plain,
    ( spl4_3
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1,sK0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f54,plain,
    ( spl4_7
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f58,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,sK0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK0,X1)) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f55,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f49,f54,f51])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f16,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f16,f15])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f37,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f28,f35])).

fof(f28,plain,
    ( spl4_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,sK0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK0,X1)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f20,f30])).

fof(f30,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f31,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (13157)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (13160)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (13152)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (13152)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f26,f31,f37,f56,f62,f77,f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ~spl4_6),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    $false | ~spl4_6),
% 0.21/0.43    inference(resolution,[],[f52,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1)) ) | ~spl4_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl4_6 <=> ! [X1,X0] : ~r1_xboole_0(X0,X1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl4_1 | ~spl4_8),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    $false | (spl4_1 | ~spl4_8)),
% 0.21/0.43    inference(subsumption_resolution,[],[f74,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    spl4_1 <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) | ~spl4_8),
% 0.21/0.43    inference(resolution,[],[f61,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))) ) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl4_8 <=> ! [X0] : ~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl4_8 | ~spl4_3 | ~spl4_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f58,f54,f35,f60])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl4_3 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1,sK0),X1) | ~r2_hidden(X0,k9_relat_1(sK0,X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl4_7 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))) ) | (~spl4_3 | ~spl4_7)),
% 0.21/0.43    inference(resolution,[],[f55,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK0),X1) | ~r2_hidden(X0,k9_relat_1(sK0,X1))) ) | ~spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f35])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl4_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl4_6 | spl4_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f49,f54,f51])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(superposition,[],[f16,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(resolution,[],[f16,f15])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl4_3 | ~spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f28,f35])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl4_2 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK0),X1) | ~r2_hidden(X0,k9_relat_1(sK0,X1))) ) | ~spl4_2),
% 0.21/0.43    inference(resolution,[],[f20,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f28])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f12,f28])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f23])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (13152)------------------------------
% 0.21/0.43  % (13152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (13152)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (13152)Memory used [KB]: 10618
% 0.21/0.43  % (13152)Time elapsed: 0.007 s
% 0.21/0.43  % (13152)------------------------------
% 0.21/0.43  % (13152)------------------------------
% 0.21/0.43  % (13150)Success in time 0.072 s
%------------------------------------------------------------------------------
