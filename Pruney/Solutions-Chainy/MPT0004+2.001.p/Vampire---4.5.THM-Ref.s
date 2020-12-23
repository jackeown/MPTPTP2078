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
% DateTime   : Thu Dec  3 12:29:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 178 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f67,f75])).

fof(f75,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f73,f30])).

fof(f30,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f22,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f73,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f41,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f36,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f36,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f41,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_2
  <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f67,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f60,f37])).

fof(f37,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f60,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f27,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f47,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f45,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,
    ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_3
  <=> ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,
    ( spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f21,f35,f44])).

fof(f21,plain,(
    ! [X3] :
      ( r1_xboole_0(sK0,sK1)
      | ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( r1_xboole_0(sK0,sK1)
      & r2_hidden(sK2,k3_xboole_0(sK0,sK1)) )
    | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
      & ~ r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK0,sK1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
        & ~ r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1))
   => r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f42,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f18,f39,f35])).

fof(f18,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:08:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.42  % (7159)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.42  % (7161)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.19/0.42  % (7165)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (7164)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.42  % (7161)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f42,f46,f67,f75])).
% 0.19/0.42  fof(f75,plain,(
% 0.19/0.42    ~spl4_1 | ~spl4_2),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f74])).
% 0.19/0.42  fof(f74,plain,(
% 0.19/0.42    $false | (~spl4_1 | ~spl4_2)),
% 0.19/0.42    inference(subsumption_resolution,[],[f73,f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f22,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(rectify,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    v1_xboole_0(k1_xboole_0)),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    v1_xboole_0(k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.42  fof(f73,plain,(
% 0.19/0.42    r2_hidden(sK2,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 0.19/0.42    inference(backward_demodulation,[],[f41,f71])).
% 0.19/0.42  fof(f71,plain,(
% 0.19/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_1),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f36,f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(nnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    r1_xboole_0(sK0,sK1) | ~spl4_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f35])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | ~spl4_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f39])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    spl4_2 <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.42  fof(f67,plain,(
% 0.19/0.42    spl4_1 | ~spl4_3),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f66])).
% 0.19/0.42  fof(f66,plain,(
% 0.19/0.42    $false | (spl4_1 | ~spl4_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f60,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ~r1_xboole_0(sK0,sK1) | spl4_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f35])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    r1_xboole_0(sK0,sK1) | ~spl4_3),
% 0.19/0.42    inference(trivial_inequality_removal,[],[f59])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl4_3),
% 0.19/0.42    inference(superposition,[],[f27,f50])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_3),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f47,f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    v1_xboole_0(k3_xboole_0(sK0,sK1)) | ~spl4_3),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f45,f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f16])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    ( ! [X3] : (~r2_hidden(X3,k3_xboole_0(sK0,sK1))) ) | ~spl4_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f44])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    spl4_3 <=> ! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    spl4_3 | spl4_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f21,f35,f44])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ( ! [X3] : (r1_xboole_0(sK0,sK1) | ~r2_hidden(X3,k3_xboole_0(sK0,sK1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    (r1_xboole_0(sK0,sK1) & r2_hidden(sK2,k3_xboole_0(sK0,sK1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1)) & ~r1_xboole_0(sK0,sK1))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11,f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1))) => ((r1_xboole_0(sK0,sK1) & ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1)) & ~r1_xboole_0(sK0,sK1)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1)) => r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(rectify,[],[f6])).
% 0.19/0.42  fof(f6,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(negated_conjecture,[],[f5])).
% 0.19/0.42  fof(f5,conjecture,(
% 0.19/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ~spl4_1 | spl4_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f18,f39,f35])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (7161)------------------------------
% 0.19/0.42  % (7161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (7161)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (7161)Memory used [KB]: 6140
% 0.19/0.42  % (7161)Time elapsed: 0.005 s
% 0.19/0.42  % (7161)------------------------------
% 0.19/0.42  % (7161)------------------------------
% 0.19/0.43  % (7158)Success in time 0.074 s
%------------------------------------------------------------------------------
