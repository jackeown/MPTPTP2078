%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :    5
%              Number of atoms          :  159 ( 240 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f61,f66,f79,f86,f91,f111,f118])).

fof(f118,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f29,f33,f110,f110,f85])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k10_relat_1(X0,X1) = X2 )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_13
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k10_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f110,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_17
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f33,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl6_2
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f29,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl6_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f111,plain,
    ( spl6_17
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f101,f89,f40,f109])).

fof(f40,plain,
    ( spl6_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK4(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f89,plain,
    ( spl6_14
  <=> ! [X1,X0] : ~ r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f101,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f90,f97])).

fof(f97,plain,
    ( ! [X3] : k1_xboole_0 = k10_relat_1(sK0,k3_xboole_0(X3,k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(resolution,[],[f90,f41])).

fof(f41,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f90,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,k1_xboole_0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl6_14
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f81,f77,f36,f89])).

fof(f36,plain,
    ( spl6_3
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f77,plain,
    ( spl6_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,X2)))
        | ~ r1_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f81,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(resolution,[],[f78,f37])).

fof(f37,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | ~ r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,X2))) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f86,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f17,f84])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f79,plain,
    ( spl6_12
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f71,f64,f44,f77])).

fof(f44,plain,
    ( spl6_5
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

% (32028)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f64,plain,
    ( spl6_9
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ r2_hidden(X1,k10_relat_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,X2)))
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f65,f45])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ r2_hidden(X1,k10_relat_1(sK0,X0)) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl6_9
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f62,f59,f28,f64])).

fof(f59,plain,
    ( spl6_8
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK2(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ r2_hidden(X1,k10_relat_1(sK0,X0)) )
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(resolution,[],[f60,f29])).

fof(f60,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK2(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

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
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f42,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f38,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f14,f36])).

fof(f14,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f34,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f30,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (32035)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (32029)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (32031)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (32027)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (32035)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (32027)Refutation not found, incomplete strategy% (32027)------------------------------
% 0.21/0.51  % (32027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32027)Memory used [KB]: 10490
% 0.21/0.51  % (32027)Time elapsed: 0.081 s
% 0.21/0.51  % (32027)------------------------------
% 0.21/0.51  % (32027)------------------------------
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f61,f66,f79,f86,f91,f111,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~spl6_1 | spl6_2 | ~spl6_13 | ~spl6_17),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    $false | (~spl6_1 | spl6_2 | ~spl6_13 | ~spl6_17)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f29,f33,f110,f110,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) ) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl6_13 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl6_17 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | spl6_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    spl6_2 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v1_relat_1(sK0) | ~spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    spl6_1 <=> v1_relat_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl6_17 | ~spl6_4 | ~spl6_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f101,f89,f40,f109])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    spl6_4 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl6_14 <=> ! [X1,X0] : ~r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,k1_xboole_0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_4 | ~spl6_14)),
% 0.21/0.51    inference(backward_demodulation,[],[f90,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X3] : (k1_xboole_0 = k10_relat_1(sK0,k3_xboole_0(X3,k1_xboole_0))) ) | (~spl6_4 | ~spl6_14)),
% 0.21/0.51    inference(resolution,[],[f90,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f40])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,k1_xboole_0)))) ) | ~spl6_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl6_14 | ~spl6_3 | ~spl6_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f77,f36,f89])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    spl6_3 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl6_12 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,k1_xboole_0)))) ) | (~spl6_3 | ~spl6_12)),
% 0.21/0.51    inference(resolution,[],[f78,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f36])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,X2)))) ) | ~spl6_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f17,f84])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl6_12 | ~spl6_5 | ~spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f71,f64,f44,f77])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl6_5 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  % (32028)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl6_9 <=> ! [X1,X0] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~r2_hidden(X1,k10_relat_1(sK0,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X1,X2)) ) | (~spl6_5 | ~spl6_9)),
% 0.21/0.51    inference(resolution,[],[f65,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~r2_hidden(X1,k10_relat_1(sK0,X0))) ) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl6_9 | ~spl6_1 | ~spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f62,f59,f28,f64])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl6_8 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | r2_hidden(sK2(X0,X1,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~r2_hidden(X1,k10_relat_1(sK0,X0))) ) | (~spl6_1 | ~spl6_8)),
% 0.21/0.51    inference(resolution,[],[f60,f29])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(X0,X1,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1))) ) | ~spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f59])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(X0,X1,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f14,f36])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f13,f32])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f12,f28])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32035)------------------------------
% 0.21/0.51  % (32035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32035)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32035)Memory used [KB]: 10618
% 0.21/0.51  % (32035)Time elapsed: 0.084 s
% 0.21/0.51  % (32035)------------------------------
% 0.21/0.51  % (32035)------------------------------
% 0.21/0.51  % (32025)Success in time 0.148 s
%------------------------------------------------------------------------------
