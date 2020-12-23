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
% DateTime   : Thu Dec  3 12:51:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 109 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :  209 ( 315 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f719,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f63,f71,f79,f84,f110,f115,f123,f658,f718])).

fof(f718,plain,
    ( spl5_1
    | ~ spl5_19
    | ~ spl5_113 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | spl5_1
    | ~ spl5_19
    | ~ spl5_113 ),
    inference(subsumption_resolution,[],[f685,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_19
  <=> k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f685,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl5_1
    | ~ spl5_113 ),
    inference(superposition,[],[f36,f657])).

fof(f657,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl5_113
  <=> ! [X1,X0] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f36,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl5_1
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f658,plain,
    ( spl5_113
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f654,f77,f44,f656])).

fof(f44,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( spl5_11
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f654,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f123,plain,
    ( spl5_19
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f116,f113,f39,f120])).

fof(f39,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f113,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f116,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl5_18
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f111,f108,f82,f113])).

fof(f82,plain,
    ( spl5_12
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f108,plain,
    ( spl5_17
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k7_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

% (13275)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f111,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k7_relat_1(sK2,X0) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl5_17
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f106,f69,f44,f108])).

fof(f69,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k7_relat_1(sK2,X0) )
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f70,f46])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f84,plain,
    ( spl5_12
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f80,f61,f49,f82])).

fof(f49,plain,
    ( spl5_4
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f61,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f79,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f71,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f63,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f51,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f47,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f42,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (13277)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (13276)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.45  % (13276)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f719,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f63,f71,f79,f84,f110,f115,f123,f658,f718])).
% 0.22/0.45  fof(f718,plain,(
% 0.22/0.45    spl5_1 | ~spl5_19 | ~spl5_113),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f717])).
% 0.22/0.45  fof(f717,plain,(
% 0.22/0.45    $false | (spl5_1 | ~spl5_19 | ~spl5_113)),
% 0.22/0.45    inference(subsumption_resolution,[],[f685,f122])).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | ~spl5_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f120])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    spl5_19 <=> k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.45  fof(f685,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | (spl5_1 | ~spl5_113)),
% 0.22/0.45    inference(superposition,[],[f36,f657])).
% 0.22/0.45  fof(f657,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl5_113),
% 0.22/0.45    inference(avatar_component_clause,[],[f656])).
% 0.22/0.45  fof(f656,plain,(
% 0.22/0.45    spl5_113 <=> ! [X1,X0] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl5_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    spl5_1 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.45  fof(f658,plain,(
% 0.22/0.45    spl5_113 | ~spl5_3 | ~spl5_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f654,f77,f44,f656])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl5_3 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    spl5_11 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.45  fof(f654,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1)) ) | (~spl5_3 | ~spl5_11)),
% 0.22/0.45    inference(resolution,[],[f78,f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl5_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) ) | ~spl5_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f77])).
% 0.22/0.45  fof(f123,plain,(
% 0.22/0.45    spl5_19 | ~spl5_2 | ~spl5_18),
% 0.22/0.45    inference(avatar_split_clause,[],[f116,f113,f39,f120])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    spl5_2 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    spl5_18 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | (~spl5_2 | ~spl5_18)),
% 0.22/0.45    inference(resolution,[],[f114,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    r1_xboole_0(sK0,sK1) | ~spl5_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f39])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl5_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f113])).
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    spl5_18 | ~spl5_12 | ~spl5_17),
% 0.22/0.45    inference(avatar_split_clause,[],[f111,f108,f82,f113])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl5_12 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    spl5_17 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k7_relat_1(sK2,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.45  % (13275)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | (~spl5_12 | ~spl5_17)),
% 0.22/0.45    inference(resolution,[],[f109,f83])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2)) ) | ~spl5_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f82])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k7_relat_1(sK2,X0)) ) | ~spl5_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f108])).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    spl5_17 | ~spl5_3 | ~spl5_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f106,f69,f44,f108])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    spl5_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k7_relat_1(sK2,X0)) ) | (~spl5_3 | ~spl5_9)),
% 0.22/0.45    inference(resolution,[],[f70,f46])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0) ) | ~spl5_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f69])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    spl5_12 | ~spl5_4 | ~spl5_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f80,f61,f49,f82])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl5_4 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl5_7 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2)) ) | (~spl5_4 | ~spl5_7)),
% 0.22/0.45    inference(resolution,[],[f62,f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f49])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl5_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f61])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    spl5_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f77])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    spl5_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f31,f69])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(nnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    spl5_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f61])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(rectify,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl5_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f49])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(rectify,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl5_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f44])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0 & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0 & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0 & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.22/0.45    inference(negated_conjecture,[],[f5])).
% 0.22/0.45  fof(f5,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl5_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f39])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    r1_xboole_0(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f34])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (13276)------------------------------
% 0.22/0.45  % (13276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (13276)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (13276)Memory used [KB]: 11001
% 0.22/0.45  % (13276)Time elapsed: 0.014 s
% 0.22/0.45  % (13276)------------------------------
% 0.22/0.45  % (13276)------------------------------
% 0.22/0.45  % (13270)Success in time 0.085 s
%------------------------------------------------------------------------------
