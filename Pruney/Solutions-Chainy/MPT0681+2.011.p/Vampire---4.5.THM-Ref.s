%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 171 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :    7
%              Number of atoms          :  290 ( 549 expanded)
%              Number of equality atoms :   62 (  96 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f71,f79,f83,f87,f107,f111,f121,f127,f134,f145,f161,f174,f206])).

fof(f206,plain,
    ( spl3_1
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl3_1
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f204,f34])).

fof(f34,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f204,plain,
    ( r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f200,f144])).

fof(f144,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_22
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f200,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
    | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(superposition,[],[f173,f106])).

fof(f106,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1))
        | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1))
        | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f174,plain,
    ( spl3_26
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f164,f159,f77,f172])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f159,plain,
    ( spl3_24
  <=> ! [X1,X0] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1))
        | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(superposition,[],[f78,f160])).

fof(f160,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f159])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f161,plain,
    ( spl3_24
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f157,f85,f52,f47,f37,f159])).

fof(f37,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f52,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f157,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f156,f54])).

fof(f54,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f155,f49])).

fof(f49,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f86,f39])).

fof(f39,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f145,plain,
    ( spl3_22
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f136,f132,f125,f142])).

fof(f125,plain,
    ( spl3_19
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f132,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k9_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f136,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(resolution,[],[f133,f126])).

fof(f126,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k9_relat_1(sK2,X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl3_20
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f130,f61,f52,f132])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k9_relat_1(sK2,X0) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f62,f54])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f127,plain,
    ( spl3_19
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f123,f119,f77,f125])).

% (2010)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f119,plain,
    ( spl3_18
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f123,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(superposition,[],[f78,f120])).

fof(f120,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f117,f109,f57,f119])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f109,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f117,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( ! [X0] :
        ( X0 != X0
        | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(superposition,[],[f110,f58])).

fof(f58,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( spl3_17
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f102,f81,f69,f109])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f81,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | k4_xboole_0(X0,X1) != X0 )
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(resolution,[],[f82,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f107,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f101,f81,f42,f104])).

fof(f42,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f101,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f82,f44])).

fof(f44,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f87,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f30,f85])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f83,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f28,f81])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f79,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f52])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f32])).

fof(f22,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (2015)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (2014)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (2014)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f71,f79,f83,f87,f107,f111,f121,f127,f134,f145,f161,f174,f206])).
% 0.21/0.42  fof(f206,plain,(
% 0.21/0.42    spl3_1 | ~spl3_16 | ~spl3_22 | ~spl3_26),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.42  fof(f205,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_16 | ~spl3_22 | ~spl3_26)),
% 0.21/0.42    inference(subsumption_resolution,[],[f204,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl3_1 <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f204,plain,(
% 0.21/0.42    r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl3_16 | ~spl3_22 | ~spl3_26)),
% 0.21/0.42    inference(subsumption_resolution,[],[f200,f144])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl3_22),
% 0.21/0.42    inference(avatar_component_clause,[],[f142])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    spl3_22 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.42  fof(f200,plain,(
% 0.21/0.42    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl3_16 | ~spl3_26)),
% 0.21/0.42    inference(superposition,[],[f173,f106])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f104])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    spl3_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.42  fof(f173,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1)) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl3_26),
% 0.21/0.42    inference(avatar_component_clause,[],[f172])).
% 0.21/0.42  fof(f172,plain,(
% 0.21/0.42    spl3_26 <=> ! [X1,X0] : (k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1)) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.42  fof(f174,plain,(
% 0.21/0.42    spl3_26 | ~spl3_11 | ~spl3_24),
% 0.21/0.42    inference(avatar_split_clause,[],[f164,f159,f77,f172])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl3_11 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.42  fof(f159,plain,(
% 0.21/0.42    spl3_24 <=> ! [X1,X0] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.42  fof(f164,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1)) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_11 | ~spl3_24)),
% 0.21/0.42    inference(superposition,[],[f78,f160])).
% 0.21/0.42  fof(f160,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl3_24),
% 0.21/0.42    inference(avatar_component_clause,[],[f159])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f77])).
% 0.21/0.42  fof(f161,plain,(
% 0.21/0.42    spl3_24 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f157,f85,f52,f47,f37,f159])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl3_4 <=> v1_funct_1(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl3_13 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.42  fof(f157,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f156,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f52])).
% 0.21/0.42  fof(f156,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) ) | (~spl3_2 | ~spl3_4 | ~spl3_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f155,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    v1_funct_1(sK2) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f47])).
% 0.21/0.42  fof(f155,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl3_2 | ~spl3_13)),
% 0.21/0.42    inference(resolution,[],[f86,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl3_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f85])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    spl3_22 | ~spl3_19 | ~spl3_20),
% 0.21/0.42    inference(avatar_split_clause,[],[f136,f132,f125,f142])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    spl3_19 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl3_20 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.42  fof(f136,plain,(
% 0.21/0.42    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | (~spl3_19 | ~spl3_20)),
% 0.21/0.42    inference(resolution,[],[f133,f126])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f125])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0)) ) | ~spl3_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f132])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    spl3_20 | ~spl3_5 | ~spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f130,f61,f52,f132])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl3_7 <=> ! [X1,X0] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0)) ) | (~spl3_5 | ~spl3_7)),
% 0.21/0.42    inference(resolution,[],[f62,f54])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) ) | ~spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    spl3_19 | ~spl3_11 | ~spl3_18),
% 0.21/0.42    inference(avatar_split_clause,[],[f123,f119,f77,f125])).
% 0.21/0.42  % (2010)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl3_18 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl3_11 | ~spl3_18)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f122])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,k1_xboole_0)) ) | (~spl3_11 | ~spl3_18)),
% 0.21/0.42    inference(superposition,[],[f78,f120])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f119])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    spl3_18 | ~spl3_6 | ~spl3_17),
% 0.21/0.42    inference(avatar_split_clause,[],[f117,f109,f57,f119])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl3_6 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    spl3_17 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_6 | ~spl3_17)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f114])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    ( ! [X0] : (X0 != X0 | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_6 | ~spl3_17)),
% 0.21/0.42    inference(superposition,[],[f110,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f109])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl3_17 | ~spl3_9 | ~spl3_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f102,f81,f69,f109])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl3_9 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl3_12 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | k4_xboole_0(X0,X1) != X0) ) | (~spl3_9 | ~spl3_12)),
% 0.21/0.42    inference(resolution,[],[f82,f70])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) ) | ~spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f69])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f81])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl3_16 | ~spl3_3 | ~spl3_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f101,f81,f42,f104])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_12)),
% 0.21/0.42    inference(resolution,[],[f82,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl3_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f85])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl3_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f81])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    spl3_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f77])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f69])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(nnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl3_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f57])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f52])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    v1_funct_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f42])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f37])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    v2_funct_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f32])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2014)------------------------------
% 0.21/0.42  % (2014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2014)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2014)Memory used [KB]: 10618
% 0.21/0.42  % (2014)Time elapsed: 0.009 s
% 0.21/0.42  % (2014)------------------------------
% 0.21/0.42  % (2014)------------------------------
% 0.21/0.43  % (2005)Success in time 0.069 s
%------------------------------------------------------------------------------
