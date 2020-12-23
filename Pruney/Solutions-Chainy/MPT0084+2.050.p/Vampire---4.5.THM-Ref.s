%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:21 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 155 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :    6
%              Number of atoms          :  254 ( 394 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2027,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f71,f75,f79,f85,f93,f122,f398,f454,f641,f1800,f2001,f2009,f2026])).

% (6948)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f2026,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_381 ),
    inference(avatar_contradiction_clause,[],[f2025])).

fof(f2025,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_381 ),
    inference(subsumption_resolution,[],[f2020,f46])).

fof(f46,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f2020,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_5
    | ~ spl3_381 ),
    inference(resolution,[],[f2008,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f2008,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_381 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f2006,plain,
    ( spl3_381
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_381])])).

fof(f2009,plain,
    ( spl3_381
    | ~ spl3_7
    | ~ spl3_380 ),
    inference(avatar_split_clause,[],[f2002,f1998,f61,f2006])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1998,plain,
    ( spl3_380
  <=> r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_380])])).

fof(f2002,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_380 ),
    inference(resolution,[],[f2000,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f2000,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0)
    | ~ spl3_380 ),
    inference(avatar_component_clause,[],[f1998])).

fof(f2001,plain,
    ( spl3_380
    | ~ spl3_81
    | ~ spl3_340 ),
    inference(avatar_split_clause,[],[f1935,f1798,f452,f1998])).

fof(f452,plain,
    ( spl3_81
  <=> ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f1798,plain,
    ( spl3_340
  <=> ! [X7] :
        ( ~ r1_tarski(k3_xboole_0(sK1,X7),sK2)
        | r1_xboole_0(k3_xboole_0(sK1,X7),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_340])])).

fof(f1935,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0)
    | ~ spl3_81
    | ~ spl3_340 ),
    inference(resolution,[],[f1799,f453])).

fof(f453,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),sK2)
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f452])).

fof(f1799,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k3_xboole_0(sK1,X7),sK2)
        | r1_xboole_0(k3_xboole_0(sK1,X7),sK0) )
    | ~ spl3_340 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f1800,plain,
    ( spl3_340
    | ~ spl3_19
    | ~ spl3_117 ),
    inference(avatar_split_clause,[],[f1774,f639,f120,f1798])).

fof(f120,plain,
    ( spl3_19
  <=> ! [X1] :
        ( r1_xboole_0(X1,sK0)
        | ~ r1_tarski(X1,k3_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f639,plain,
    ( spl3_117
  <=> ! [X1,X3,X2] :
        ( ~ r1_tarski(k3_xboole_0(X1,X2),X3)
        | r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_117])])).

fof(f1774,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k3_xboole_0(sK1,X7),sK2)
        | r1_xboole_0(k3_xboole_0(sK1,X7),sK0) )
    | ~ spl3_19
    | ~ spl3_117 ),
    inference(resolution,[],[f640,f121])).

fof(f121,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k3_xboole_0(sK1,sK2))
        | r1_xboole_0(X1,sK0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f640,plain,
    ( ! [X2,X3,X1] :
        ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))
        | ~ r1_tarski(k3_xboole_0(X1,X2),X3) )
    | ~ spl3_117 ),
    inference(avatar_component_clause,[],[f639])).

fof(f641,plain,
    ( spl3_117
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f623,f77,f49,f639])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f623,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(k3_xboole_0(X1,X2),X3)
        | r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) )
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f78,f50])).

fof(f50,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X2)
        | r1_tarski(X0,k3_xboole_0(X1,X2)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f454,plain,
    ( spl3_81
    | ~ spl3_13
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f434,f396,f90,f452])).

fof(f90,plain,
    ( spl3_13
  <=> sK2 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f396,plain,
    ( spl3_69
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f434,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),sK2)
    | ~ spl3_13
    | ~ spl3_69 ),
    inference(superposition,[],[f397,f92])).

fof(f92,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f397,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f396])).

fof(f398,plain,
    ( spl3_69
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f386,f69,f65,f396])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f386,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(resolution,[],[f66,f70])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f66,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f122,plain,
    ( spl3_19
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f114,f82,f73,f120])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f82,plain,
    ( spl3_12
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f114,plain,
    ( ! [X1] :
        ( r1_xboole_0(X1,sK0)
        | ~ r1_tarski(X1,k3_xboole_0(sK1,sK2)) )
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(resolution,[],[f74,f84])).

fof(f84,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f93,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f87,f57,f39,f90])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f87,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f85,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f80,f53,f34,f82])).

fof(f34,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f79,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f75,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:20:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.40  % (6945)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.18/0.43  % (6950)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.18/0.43  % (6946)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.18/0.44  % (6942)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.18/0.45  % (6952)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.18/0.46  % (6943)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.18/0.47  % (6951)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.18/0.47  % (6944)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.18/0.47  % (6946)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f2027,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f71,f75,f79,f85,f93,f122,f398,f454,f641,f1800,f2001,f2009,f2026])).
% 0.18/0.47  % (6948)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.18/0.47  fof(f2026,plain,(
% 0.18/0.47    spl3_3 | ~spl3_5 | ~spl3_381),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f2025])).
% 0.18/0.47  fof(f2025,plain,(
% 0.18/0.47    $false | (spl3_3 | ~spl3_5 | ~spl3_381)),
% 0.18/0.47    inference(subsumption_resolution,[],[f2020,f46])).
% 0.18/0.47  fof(f46,plain,(
% 0.18/0.47    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f44])).
% 0.18/0.47  fof(f44,plain,(
% 0.18/0.47    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.47  fof(f2020,plain,(
% 0.18/0.47    r1_xboole_0(sK0,sK1) | (~spl3_5 | ~spl3_381)),
% 0.18/0.47    inference(resolution,[],[f2008,f54])).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f53])).
% 0.18/0.47  fof(f53,plain,(
% 0.18/0.47    spl3_5 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.47  fof(f2008,plain,(
% 0.18/0.47    r1_xboole_0(sK1,sK0) | ~spl3_381),
% 0.18/0.47    inference(avatar_component_clause,[],[f2006])).
% 0.18/0.47  fof(f2006,plain,(
% 0.18/0.47    spl3_381 <=> r1_xboole_0(sK1,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_381])])).
% 0.18/0.47  fof(f2009,plain,(
% 0.18/0.47    spl3_381 | ~spl3_7 | ~spl3_380),
% 0.18/0.47    inference(avatar_split_clause,[],[f2002,f1998,f61,f2006])).
% 0.18/0.47  fof(f61,plain,(
% 0.18/0.47    spl3_7 <=> ! [X1,X0] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.18/0.47  fof(f1998,plain,(
% 0.18/0.47    spl3_380 <=> r1_xboole_0(k3_xboole_0(sK1,sK0),sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_380])])).
% 0.18/0.47  fof(f2002,plain,(
% 0.18/0.47    r1_xboole_0(sK1,sK0) | (~spl3_7 | ~spl3_380)),
% 0.18/0.47    inference(resolution,[],[f2000,f62])).
% 0.18/0.47  fof(f62,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.18/0.47    inference(avatar_component_clause,[],[f61])).
% 0.18/0.47  fof(f2000,plain,(
% 0.18/0.47    r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) | ~spl3_380),
% 0.18/0.47    inference(avatar_component_clause,[],[f1998])).
% 0.18/0.47  fof(f2001,plain,(
% 0.18/0.47    spl3_380 | ~spl3_81 | ~spl3_340),
% 0.18/0.47    inference(avatar_split_clause,[],[f1935,f1798,f452,f1998])).
% 0.18/0.47  fof(f452,plain,(
% 0.18/0.47    spl3_81 <=> ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 0.18/0.47  fof(f1798,plain,(
% 0.18/0.47    spl3_340 <=> ! [X7] : (~r1_tarski(k3_xboole_0(sK1,X7),sK2) | r1_xboole_0(k3_xboole_0(sK1,X7),sK0))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_340])])).
% 0.18/0.47  fof(f1935,plain,(
% 0.18/0.47    r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) | (~spl3_81 | ~spl3_340)),
% 0.18/0.47    inference(resolution,[],[f1799,f453])).
% 0.18/0.47  fof(f453,plain,(
% 0.18/0.47    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),sK2)) ) | ~spl3_81),
% 0.18/0.47    inference(avatar_component_clause,[],[f452])).
% 0.18/0.47  fof(f1799,plain,(
% 0.18/0.47    ( ! [X7] : (~r1_tarski(k3_xboole_0(sK1,X7),sK2) | r1_xboole_0(k3_xboole_0(sK1,X7),sK0)) ) | ~spl3_340),
% 0.18/0.47    inference(avatar_component_clause,[],[f1798])).
% 0.18/0.47  fof(f1800,plain,(
% 0.18/0.47    spl3_340 | ~spl3_19 | ~spl3_117),
% 0.18/0.47    inference(avatar_split_clause,[],[f1774,f639,f120,f1798])).
% 0.18/0.47  fof(f120,plain,(
% 0.18/0.47    spl3_19 <=> ! [X1] : (r1_xboole_0(X1,sK0) | ~r1_tarski(X1,k3_xboole_0(sK1,sK2)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.18/0.47  fof(f639,plain,(
% 0.18/0.47    spl3_117 <=> ! [X1,X3,X2] : (~r1_tarski(k3_xboole_0(X1,X2),X3) | r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_117])])).
% 0.18/0.47  fof(f1774,plain,(
% 0.18/0.47    ( ! [X7] : (~r1_tarski(k3_xboole_0(sK1,X7),sK2) | r1_xboole_0(k3_xboole_0(sK1,X7),sK0)) ) | (~spl3_19 | ~spl3_117)),
% 0.18/0.47    inference(resolution,[],[f640,f121])).
% 0.18/0.47  fof(f121,plain,(
% 0.18/0.47    ( ! [X1] : (~r1_tarski(X1,k3_xboole_0(sK1,sK2)) | r1_xboole_0(X1,sK0)) ) | ~spl3_19),
% 0.18/0.47    inference(avatar_component_clause,[],[f120])).
% 0.18/0.47  fof(f640,plain,(
% 0.18/0.47    ( ! [X2,X3,X1] : (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(k3_xboole_0(X1,X2),X3)) ) | ~spl3_117),
% 0.18/0.47    inference(avatar_component_clause,[],[f639])).
% 0.18/0.47  fof(f641,plain,(
% 0.18/0.47    spl3_117 | ~spl3_4 | ~spl3_11),
% 0.18/0.47    inference(avatar_split_clause,[],[f623,f77,f49,f639])).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    spl3_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.18/0.47  fof(f77,plain,(
% 0.18/0.47    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.18/0.47  fof(f623,plain,(
% 0.18/0.47    ( ! [X2,X3,X1] : (~r1_tarski(k3_xboole_0(X1,X2),X3) | r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))) ) | (~spl3_4 | ~spl3_11)),
% 0.18/0.47    inference(resolution,[],[f78,f50])).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f49])).
% 0.18/0.47  fof(f78,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) ) | ~spl3_11),
% 0.18/0.47    inference(avatar_component_clause,[],[f77])).
% 0.18/0.47  fof(f454,plain,(
% 0.18/0.47    spl3_81 | ~spl3_13 | ~spl3_69),
% 0.18/0.47    inference(avatar_split_clause,[],[f434,f396,f90,f452])).
% 0.18/0.47  fof(f90,plain,(
% 0.18/0.47    spl3_13 <=> sK2 = k2_xboole_0(sK0,sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.18/0.47  fof(f396,plain,(
% 0.18/0.47    spl3_69 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.18/0.47  fof(f434,plain,(
% 0.18/0.47    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),sK2)) ) | (~spl3_13 | ~spl3_69)),
% 0.18/0.47    inference(superposition,[],[f397,f92])).
% 0.18/0.47  fof(f92,plain,(
% 0.18/0.47    sK2 = k2_xboole_0(sK0,sK2) | ~spl3_13),
% 0.18/0.47    inference(avatar_component_clause,[],[f90])).
% 0.18/0.47  fof(f397,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))) ) | ~spl3_69),
% 0.18/0.47    inference(avatar_component_clause,[],[f396])).
% 0.18/0.47  fof(f398,plain,(
% 0.18/0.47    spl3_69 | ~spl3_8 | ~spl3_9),
% 0.18/0.47    inference(avatar_split_clause,[],[f386,f69,f65,f396])).
% 0.18/0.47  fof(f65,plain,(
% 0.18/0.47    spl3_8 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.18/0.47  fof(f69,plain,(
% 0.18/0.47    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.18/0.47  fof(f386,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))) ) | (~spl3_8 | ~spl3_9)),
% 0.18/0.47    inference(resolution,[],[f66,f70])).
% 0.18/0.47  fof(f70,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl3_9),
% 0.18/0.47    inference(avatar_component_clause,[],[f69])).
% 0.18/0.47  fof(f66,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl3_8),
% 0.18/0.47    inference(avatar_component_clause,[],[f65])).
% 0.18/0.47  fof(f122,plain,(
% 0.18/0.47    spl3_19 | ~spl3_10 | ~spl3_12),
% 0.18/0.47    inference(avatar_split_clause,[],[f114,f82,f73,f120])).
% 0.18/0.47  fof(f73,plain,(
% 0.18/0.47    spl3_10 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.18/0.47  fof(f82,plain,(
% 0.18/0.47    spl3_12 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.18/0.47  fof(f114,plain,(
% 0.18/0.47    ( ! [X1] : (r1_xboole_0(X1,sK0) | ~r1_tarski(X1,k3_xboole_0(sK1,sK2))) ) | (~spl3_10 | ~spl3_12)),
% 0.18/0.47    inference(resolution,[],[f74,f84])).
% 0.18/0.47  fof(f84,plain,(
% 0.18/0.47    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl3_12),
% 0.18/0.47    inference(avatar_component_clause,[],[f82])).
% 0.18/0.47  fof(f74,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.18/0.47    inference(avatar_component_clause,[],[f73])).
% 0.18/0.47  fof(f93,plain,(
% 0.18/0.47    spl3_13 | ~spl3_2 | ~spl3_6),
% 0.18/0.47    inference(avatar_split_clause,[],[f87,f57,f39,f90])).
% 0.18/0.47  fof(f39,plain,(
% 0.18/0.47    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.47  fof(f57,plain,(
% 0.18/0.47    spl3_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.47  fof(f87,plain,(
% 0.18/0.47    sK2 = k2_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_6)),
% 0.18/0.47    inference(resolution,[],[f58,f41])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f39])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_6),
% 0.18/0.47    inference(avatar_component_clause,[],[f57])).
% 0.18/0.47  fof(f85,plain,(
% 0.18/0.47    spl3_12 | ~spl3_1 | ~spl3_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f80,f53,f34,f82])).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    spl3_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.47  fof(f80,plain,(
% 0.18/0.47    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | (~spl3_1 | ~spl3_5)),
% 0.18/0.47    inference(resolution,[],[f54,f36])).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f34])).
% 0.18/0.47  fof(f79,plain,(
% 0.18/0.47    spl3_11),
% 0.18/0.47    inference(avatar_split_clause,[],[f32,f77])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.18/0.47    inference(flattening,[],[f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.18/0.47    inference(ennf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.18/0.47  fof(f75,plain,(
% 0.18/0.47    spl3_10),
% 0.18/0.47    inference(avatar_split_clause,[],[f31,f73])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.18/0.47    inference(flattening,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.18/0.47    inference(ennf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.18/0.47  fof(f71,plain,(
% 0.18/0.47    spl3_9),
% 0.18/0.47    inference(avatar_split_clause,[],[f30,f69])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.18/0.47    inference(ennf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.18/0.47  fof(f67,plain,(
% 0.18/0.47    spl3_8),
% 0.18/0.47    inference(avatar_split_clause,[],[f29,f65])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.18/0.47  fof(f63,plain,(
% 0.18/0.47    spl3_7),
% 0.18/0.47    inference(avatar_split_clause,[],[f28,f61])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f14])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.18/0.47  fof(f59,plain,(
% 0.18/0.47    spl3_6),
% 0.18/0.47    inference(avatar_split_clause,[],[f27,f57])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f13])).
% 0.18/0.47  fof(f13,plain,(
% 0.18/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.18/0.47  fof(f55,plain,(
% 0.18/0.47    spl3_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f26,f53])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f12])).
% 0.18/0.47  fof(f12,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.18/0.47  fof(f51,plain,(
% 0.18/0.47    spl3_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f25,f49])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.18/0.47  fof(f47,plain,(
% 0.18/0.47    ~spl3_3),
% 0.18/0.47    inference(avatar_split_clause,[],[f22,f44])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ~r1_xboole_0(sK0,sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f11,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.18/0.47    inference(negated_conjecture,[],[f9])).
% 0.18/0.47  fof(f9,conjecture,(
% 0.18/0.47    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    spl3_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f23,f39])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    r1_tarski(sK0,sK2)),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    spl3_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f24,f34])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (6946)------------------------------
% 0.18/0.47  % (6946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (6946)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (6946)Memory used [KB]: 12025
% 0.18/0.47  % (6946)Time elapsed: 0.042 s
% 0.18/0.47  % (6946)------------------------------
% 0.18/0.47  % (6946)------------------------------
% 0.18/0.48  % (6938)Success in time 0.141 s
%------------------------------------------------------------------------------
