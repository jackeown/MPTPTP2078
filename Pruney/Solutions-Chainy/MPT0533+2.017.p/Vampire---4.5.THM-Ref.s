%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 205 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :    7
%              Number of atoms          :  366 ( 719 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2772,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f58,f62,f66,f70,f74,f78,f82,f94,f127,f229,f233,f239,f244,f260,f307,f461,f2688,f2737,f2771])).

fof(f2771,plain,
    ( spl4_1
    | ~ spl4_40
    | ~ spl4_505 ),
    inference(avatar_contradiction_clause,[],[f2770])).

fof(f2770,plain,
    ( $false
    | spl4_1
    | ~ spl4_40
    | ~ spl4_505 ),
    inference(subsumption_resolution,[],[f2749,f37])).

fof(f37,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_1
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2749,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | ~ spl4_40
    | ~ spl4_505 ),
    inference(resolution,[],[f2736,f243])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relat_1(X0,sK3),X1)
        | r1_tarski(k8_relat_1(X0,sK2),X1) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_40
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k8_relat_1(X0,sK3),X1)
        | r1_tarski(k8_relat_1(X0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f2736,plain,
    ( r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))
    | ~ spl4_505 ),
    inference(avatar_component_clause,[],[f2734])).

fof(f2734,plain,
    ( spl4_505
  <=> r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_505])])).

fof(f2737,plain,
    ( spl4_505
    | ~ spl4_51
    | ~ spl4_496 ),
    inference(avatar_split_clause,[],[f2702,f2686,f304,f2734])).

fof(f304,plain,
    ( spl4_51
  <=> k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f2686,plain,
    ( spl4_496
  <=> ! [X3,X2] : r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_496])])).

fof(f2702,plain,
    ( r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))
    | ~ spl4_51
    | ~ spl4_496 ),
    inference(superposition,[],[f2687,f306])).

fof(f306,plain,
    ( k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f304])).

fof(f2687,plain,
    ( ! [X2,X3] : r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3))
    | ~ spl4_496 ),
    inference(avatar_component_clause,[],[f2686])).

fof(f2688,plain,
    ( spl4_496
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f2684,f459,f64,f50,f2686])).

fof(f50,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f64,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f459,plain,
    ( spl4_75
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k8_relat_1(X1,k8_relat_1(X2,sK3)),k8_relat_1(X1,X0))
        | ~ r1_tarski(k8_relat_1(X2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f2684,plain,
    ( ! [X2,X3] : r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3))
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f2679,f52])).

fof(f52,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f2679,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_7
    | ~ spl4_75 ),
    inference(duplicate_literal_removal,[],[f2677])).

fof(f2677,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3))
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_7
    | ~ spl4_75 ),
    inference(resolution,[],[f460,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f460,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k8_relat_1(X2,sK3),X0)
        | r1_tarski(k8_relat_1(X1,k8_relat_1(X2,sK3)),k8_relat_1(X1,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f459])).

fof(f461,plain,
    ( spl4_75
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f453,f231,f50,f459])).

fof(f231,plain,
    ( spl4_38
  <=> ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(k8_relat_1(X4,X5),X6)
        | ~ v1_relat_1(X6)
        | r1_tarski(k8_relat_1(X7,k8_relat_1(X4,X5)),k8_relat_1(X7,X6))
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f453,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k8_relat_1(X1,k8_relat_1(X2,sK3)),k8_relat_1(X1,X0))
        | ~ r1_tarski(k8_relat_1(X2,sK3),X0) )
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(resolution,[],[f232,f52])).

fof(f232,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_relat_1(X5)
        | ~ v1_relat_1(X6)
        | r1_tarski(k8_relat_1(X7,k8_relat_1(X4,X5)),k8_relat_1(X7,X6))
        | ~ r1_tarski(k8_relat_1(X4,X5),X6) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f231])).

fof(f307,plain,
    ( spl4_51
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f277,f258,f40,f304])).

fof(f40,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f258,plain,
    ( spl4_42
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f277,plain,
    ( k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(resolution,[],[f259,f42])).

fof(f42,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3)) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,
    ( spl4_42
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f254,f125,f50,f258])).

fof(f125,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3)) )
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(resolution,[],[f126,f52])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f244,plain,
    ( spl4_40
    | ~ spl4_11
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f240,f237,f80,f242])).

fof(f80,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f237,plain,
    ( spl4_39
  <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relat_1(X0,sK3),X1)
        | r1_tarski(k8_relat_1(X0,sK2),X1) )
    | ~ spl4_11
    | ~ spl4_39 ),
    inference(resolution,[],[f238,f81])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f238,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl4_39
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f235,f227,f50,f45,f237])).

fof(f45,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f227,plain,
    ( spl4_37
  <=> ! [X3,X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ v1_relat_1(X2)
        | r1_tarski(k8_relat_1(X3,sK2),k8_relat_1(X3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f235,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f234,f52])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3)) )
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(resolution,[],[f228,f47])).

fof(f47,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f228,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK2,X2)
        | ~ v1_relat_1(X2)
        | r1_tarski(k8_relat_1(X3,sK2),k8_relat_1(X3,X2)) )
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f227])).

fof(f233,plain,
    ( spl4_38
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f221,f76,f60,f231])).

fof(f60,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f221,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_tarski(k8_relat_1(X4,X5),X6)
        | ~ v1_relat_1(X6)
        | r1_tarski(k8_relat_1(X7,k8_relat_1(X4,X5)),k8_relat_1(X7,X6))
        | ~ v1_relat_1(X5) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f229,plain,
    ( spl4_37
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f220,f76,f55,f227])).

fof(f55,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f220,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK2,X2)
        | ~ v1_relat_1(X2)
        | r1_tarski(k8_relat_1(X3,sK2),k8_relat_1(X3,X2)) )
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f77,f57])).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f127,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f123,f92,f72,f60,f125])).

fof(f72,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f92,plain,
    ( spl4_13
  <=> ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,X4)
        | r1_tarski(k2_relat_1(k8_relat_1(X3,X5)),X4)
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f121,f61])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
        | ~ v1_relat_1(k8_relat_1(X0,X2)) )
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(resolution,[],[f93,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f93,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X3,X5)),X4)
        | ~ r1_tarski(X3,X4)
        | ~ v1_relat_1(X5) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl4_13
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f84,f80,f68,f92])).

fof(f68,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f84,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X3,X4)
        | r1_tarski(k2_relat_1(k8_relat_1(X3,X5)),X4)
        | ~ v1_relat_1(X5) )
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(resolution,[],[f81,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f82,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

% (2318)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f78,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f74,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f70,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f66,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f58,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f53,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f40])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f35])).

fof(f27,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:45:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (2323)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (2324)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.44  % (2321)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (2320)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.48  % (2326)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.48  % (2319)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.48  % (2316)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.48  % (2322)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.48  % (2321)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f2772,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f58,f62,f66,f70,f74,f78,f82,f94,f127,f229,f233,f239,f244,f260,f307,f461,f2688,f2737,f2771])).
% 0.21/0.48  fof(f2771,plain,(
% 0.21/0.48    spl4_1 | ~spl4_40 | ~spl4_505),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f2770])).
% 0.21/0.48  fof(f2770,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_40 | ~spl4_505)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2749,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl4_1 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f2749,plain,(
% 0.21/0.48    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | (~spl4_40 | ~spl4_505)),
% 0.21/0.48    inference(resolution,[],[f2736,f243])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k8_relat_1(X0,sK3),X1) | r1_tarski(k8_relat_1(X0,sK2),X1)) ) | ~spl4_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f242])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    spl4_40 <=> ! [X1,X0] : (~r1_tarski(k8_relat_1(X0,sK3),X1) | r1_tarski(k8_relat_1(X0,sK2),X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.48  fof(f2736,plain,(
% 0.21/0.48    r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) | ~spl4_505),
% 0.21/0.48    inference(avatar_component_clause,[],[f2734])).
% 0.21/0.48  fof(f2734,plain,(
% 0.21/0.48    spl4_505 <=> r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_505])])).
% 0.21/0.48  fof(f2737,plain,(
% 0.21/0.48    spl4_505 | ~spl4_51 | ~spl4_496),
% 0.21/0.48    inference(avatar_split_clause,[],[f2702,f2686,f304,f2734])).
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    spl4_51 <=> k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.48  fof(f2686,plain,(
% 0.21/0.48    spl4_496 <=> ! [X3,X2] : r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_496])])).
% 0.21/0.48  fof(f2702,plain,(
% 0.21/0.48    r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) | (~spl4_51 | ~spl4_496)),
% 0.21/0.48    inference(superposition,[],[f2687,f306])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) | ~spl4_51),
% 0.21/0.48    inference(avatar_component_clause,[],[f304])).
% 0.21/0.48  fof(f2687,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3))) ) | ~spl4_496),
% 0.21/0.48    inference(avatar_component_clause,[],[f2686])).
% 0.21/0.48  fof(f2688,plain,(
% 0.21/0.48    spl4_496 | ~spl4_4 | ~spl4_7 | ~spl4_75),
% 0.21/0.48    inference(avatar_split_clause,[],[f2684,f459,f64,f50,f2686])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl4_7 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f459,plain,(
% 0.21/0.48    spl4_75 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | r1_tarski(k8_relat_1(X1,k8_relat_1(X2,sK3)),k8_relat_1(X1,X0)) | ~r1_tarski(k8_relat_1(X2,sK3),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 0.21/0.48  fof(f2684,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3))) ) | (~spl4_4 | ~spl4_7 | ~spl4_75)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2679,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f2679,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3)) | ~v1_relat_1(sK3)) ) | (~spl4_7 | ~spl4_75)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f2677])).
% 0.21/0.48  fof(f2677,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,k8_relat_1(X3,sK3)),k8_relat_1(X2,sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3)) ) | (~spl4_7 | ~spl4_75)),
% 0.21/0.48    inference(resolution,[],[f460,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f460,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k8_relat_1(X2,sK3),X0) | r1_tarski(k8_relat_1(X1,k8_relat_1(X2,sK3)),k8_relat_1(X1,X0)) | ~v1_relat_1(X0)) ) | ~spl4_75),
% 0.21/0.48    inference(avatar_component_clause,[],[f459])).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    spl4_75 | ~spl4_4 | ~spl4_38),
% 0.21/0.48    inference(avatar_split_clause,[],[f453,f231,f50,f459])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl4_38 <=> ! [X5,X7,X4,X6] : (~r1_tarski(k8_relat_1(X4,X5),X6) | ~v1_relat_1(X6) | r1_tarski(k8_relat_1(X7,k8_relat_1(X4,X5)),k8_relat_1(X7,X6)) | ~v1_relat_1(X5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.48  fof(f453,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k8_relat_1(X1,k8_relat_1(X2,sK3)),k8_relat_1(X1,X0)) | ~r1_tarski(k8_relat_1(X2,sK3),X0)) ) | (~spl4_4 | ~spl4_38)),
% 0.21/0.48    inference(resolution,[],[f232,f52])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X5) | ~v1_relat_1(X6) | r1_tarski(k8_relat_1(X7,k8_relat_1(X4,X5)),k8_relat_1(X7,X6)) | ~r1_tarski(k8_relat_1(X4,X5),X6)) ) | ~spl4_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    spl4_51 | ~spl4_2 | ~spl4_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f277,f258,f40,f304])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl4_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl4_42 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) | (~spl4_2 | ~spl4_42)),
% 0.21/0.48    inference(resolution,[],[f259,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3))) ) | ~spl4_42),
% 0.21/0.48    inference(avatar_component_clause,[],[f258])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    spl4_42 | ~spl4_4 | ~spl4_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f254,f125,f50,f258])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl4_19 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3))) ) | (~spl4_4 | ~spl4_19)),
% 0.21/0.48    inference(resolution,[],[f126,f52])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) ) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl4_40 | ~spl4_11 | ~spl4_39),
% 0.21/0.48    inference(avatar_split_clause,[],[f240,f237,f80,f242])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl4_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    spl4_39 <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k8_relat_1(X0,sK3),X1) | r1_tarski(k8_relat_1(X0,sK2),X1)) ) | (~spl4_11 | ~spl4_39)),
% 0.21/0.48    inference(resolution,[],[f238,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3))) ) | ~spl4_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f237])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl4_39 | ~spl4_3 | ~spl4_4 | ~spl4_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f235,f227,f50,f45,f237])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    spl4_37 <=> ! [X3,X2] : (~r1_tarski(sK2,X2) | ~v1_relat_1(X2) | r1_tarski(k8_relat_1(X3,sK2),k8_relat_1(X3,X2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3))) ) | (~spl4_3 | ~spl4_4 | ~spl4_37)),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f52])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK3) | r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3))) ) | (~spl4_3 | ~spl4_37)),
% 0.21/0.48    inference(resolution,[],[f228,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r1_tarski(sK2,X2) | ~v1_relat_1(X2) | r1_tarski(k8_relat_1(X3,sK2),k8_relat_1(X3,X2))) ) | ~spl4_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f227])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    spl4_38 | ~spl4_6 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f221,f76,f60,f231])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl4_6 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ( ! [X6,X4,X7,X5] : (~r1_tarski(k8_relat_1(X4,X5),X6) | ~v1_relat_1(X6) | r1_tarski(k8_relat_1(X7,k8_relat_1(X4,X5)),k8_relat_1(X7,X6)) | ~v1_relat_1(X5)) ) | (~spl4_6 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f77,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))) ) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    spl4_37 | ~spl4_5 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f220,f76,f55,f227])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_5 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r1_tarski(sK2,X2) | ~v1_relat_1(X2) | r1_tarski(k8_relat_1(X3,sK2),k8_relat_1(X3,X2))) ) | (~spl4_5 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f77,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl4_19 | ~spl4_6 | ~spl4_9 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f92,f72,f60,f125])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl4_9 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl4_13 <=> ! [X3,X5,X4] : (~r1_tarski(X3,X4) | r1_tarski(k2_relat_1(k8_relat_1(X3,X5)),X4) | ~v1_relat_1(X5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) ) | (~spl4_6 | ~spl4_9 | ~spl4_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f121,f61])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) ) | (~spl4_9 | ~spl4_13)),
% 0.21/0.48    inference(resolution,[],[f93,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (r1_tarski(k2_relat_1(k8_relat_1(X3,X5)),X4) | ~r1_tarski(X3,X4) | ~v1_relat_1(X5)) ) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_13 | ~spl4_8 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f80,f68,f92])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_8 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | r1_tarski(k2_relat_1(k8_relat_1(X3,X5)),X4) | ~v1_relat_1(X5)) ) | (~spl4_8 | ~spl4_11)),
% 0.21/0.48    inference(resolution,[],[f81,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) ) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f80])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  % (2318)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f76])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f72])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f68])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f64])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f60])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f55])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f50])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f45])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f40])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f35])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (2321)------------------------------
% 0.21/0.48  % (2321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2321)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (2321)Memory used [KB]: 12281
% 0.21/0.48  % (2321)Time elapsed: 0.045 s
% 0.21/0.48  % (2321)------------------------------
% 0.21/0.48  % (2321)------------------------------
% 0.21/0.49  % (2315)Success in time 0.125 s
%------------------------------------------------------------------------------
