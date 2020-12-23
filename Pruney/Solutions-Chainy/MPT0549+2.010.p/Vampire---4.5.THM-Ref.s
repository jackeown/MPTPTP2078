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
% DateTime   : Thu Dec  3 12:49:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 167 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :    6
%              Number of atoms          :  309 ( 462 expanded)
%              Number of equality atoms :   43 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21713)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f607,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f58,f61,f69,f73,f77,f90,f95,f99,f111,f115,f127,f132,f147,f157,f176,f180,f200,f294,f601,f606])).

fof(f606,plain,
    ( ~ spl7_2
    | ~ spl7_10
    | ~ spl7_27
    | ~ spl7_78 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_27
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f604,f89])).

fof(f89,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_10
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f604,plain,
    ( r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_27
    | ~ spl7_78 ),
    inference(forward_demodulation,[],[f602,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl7_2
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f602,plain,
    ( r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,sK0))
    | ~ spl7_27
    | ~ spl7_78 ),
    inference(resolution,[],[f600,f179])).

fof(f179,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl7_27
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f600,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),X0)
        | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0)) )
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl7_78
  <=> ! [X0] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),X0)
        | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f601,plain,
    ( spl7_78
    | ~ spl7_1
    | ~ spl7_26
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f301,f292,f174,f49,f599])).

fof(f49,plain,
    ( spl7_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f174,plain,
    ( spl7_26
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f292,plain,
    ( spl7_44
  <=> r2_hidden(k4_tarski(sK2(k1_relat_1(sK1),sK0),sK4(sK1,sK2(k1_relat_1(sK1),sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),X0)
        | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0)) )
    | ~ spl7_1
    | ~ spl7_26
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f298,f50])).

fof(f50,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),X0)
        | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0)) )
    | ~ spl7_26
    | ~ spl7_44 ),
    inference(resolution,[],[f293,f175])).

fof(f175,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f174])).

fof(f293,plain,
    ( r2_hidden(k4_tarski(sK2(k1_relat_1(sK1),sK0),sK4(sK1,sK2(k1_relat_1(sK1),sK0))),sK1)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f292])).

fof(f294,plain,
    ( spl7_44
    | ~ spl7_19
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f206,f198,f125,f292])).

fof(f125,plain,
    ( spl7_19
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f198,plain,
    ( spl7_31
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f206,plain,
    ( r2_hidden(k4_tarski(sK2(k1_relat_1(sK1),sK0),sK4(sK1,sK2(k1_relat_1(sK1),sK0))),sK1)
    | ~ spl7_19
    | ~ spl7_31 ),
    inference(resolution,[],[f199,f126])).

fof(f126,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_relat_1(X0))
        | r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f199,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl7_31
    | spl7_3
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f159,f93,f56,f198])).

fof(f56,plain,
    ( spl7_3
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f93,plain,
    ( spl7_11
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f159,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | spl7_3
    | ~ spl7_11 ),
    inference(resolution,[],[f60,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f60,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f180,plain,
    ( spl7_27
    | spl7_3
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f158,f97,f56,f178])).

fof(f97,plain,
    ( spl7_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f158,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)
    | spl7_3
    | ~ spl7_12 ),
    inference(resolution,[],[f60,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X1) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f176,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f47,f174])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f157,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f154,f57])).

fof(f57,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f154,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl7_2
    | ~ spl7_22 ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl7_2
    | ~ spl7_22 ),
    inference(superposition,[],[f59,f146])).

fof(f146,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k9_relat_1(sK1,X1)
        | ~ r1_xboole_0(k1_relat_1(sK1),X1) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_22
  <=> ! [X1] :
        ( k1_xboole_0 = k9_relat_1(sK1,X1)
        | ~ r1_xboole_0(k1_relat_1(sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f59,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f147,plain,
    ( spl7_22
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f138,f130,f109,f67,f49,f145])).

fof(f67,plain,
    ( spl7_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f109,plain,
    ( spl7_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f130,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f138,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k9_relat_1(sK1,X1)
        | ~ r1_xboole_0(k1_relat_1(sK1),X1) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f137,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f137,plain,
    ( ! [X1] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,X1)
        | ~ r1_xboole_0(k1_relat_1(sK1),X1) )
    | ~ spl7_1
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f136,f50])).

fof(f136,plain,
    ( ! [X1] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1)
        | ~ r1_xboole_0(k1_relat_1(sK1),X1) )
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(superposition,[],[f110,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | ~ r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f130])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f132,plain,
    ( spl7_20
    | ~ spl7_1
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f128,f113,f49,f130])).

fof(f113,plain,
    ( spl7_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl7_1
    | ~ spl7_16 ),
    inference(resolution,[],[f114,f50])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f113])).

fof(f127,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f43,f125])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f115,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f29,f113])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f111,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f28,f109])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f99,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f27,f97])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f95,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f26,f93])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,
    ( spl7_10
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f86,f75,f71,f88])).

fof(f71,plain,
    ( spl7_6
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f75,plain,
    ( spl7_7
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f86,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f72,f76])).

fof(f76,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f72,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f77,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f73,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f24,f71])).

fof(f24,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f69,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f23,f67])).

fof(f23,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f61,plain,
    ( ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f20,f56,f53])).

fof(f20,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f58,plain,
    ( spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f19,f56,f53])).

fof(f19,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (21705)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (21710)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (21718)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (21720)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (21714)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (21725)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (21725)Refutation not found, incomplete strategy% (21725)------------------------------
% 0.21/0.48  % (21725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21725)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21725)Memory used [KB]: 10618
% 0.21/0.48  % (21725)Time elapsed: 0.062 s
% 0.21/0.48  % (21725)------------------------------
% 0.21/0.48  % (21725)------------------------------
% 0.21/0.48  % (21706)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21712)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (21721)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (21707)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (21719)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (21716)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (21715)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (21709)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (21715)Refutation not found, incomplete strategy% (21715)------------------------------
% 0.21/0.49  % (21715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21715)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21715)Memory used [KB]: 6012
% 0.21/0.49  % (21715)Time elapsed: 0.085 s
% 0.21/0.49  % (21715)------------------------------
% 0.21/0.49  % (21715)------------------------------
% 0.21/0.50  % (21711)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (21706)Refutation not found, incomplete strategy% (21706)------------------------------
% 0.21/0.50  % (21706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21706)Memory used [KB]: 10618
% 0.21/0.50  % (21706)Time elapsed: 0.093 s
% 0.21/0.50  % (21706)------------------------------
% 0.21/0.50  % (21706)------------------------------
% 0.21/0.50  % (21723)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (21714)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (21713)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  fof(f607,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f51,f58,f61,f69,f73,f77,f90,f95,f99,f111,f115,f127,f132,f147,f157,f176,f180,f200,f294,f601,f606])).
% 0.21/0.50  fof(f606,plain,(
% 0.21/0.50    ~spl7_2 | ~spl7_10 | ~spl7_27 | ~spl7_78),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f605])).
% 0.21/0.50  fof(f605,plain,(
% 0.21/0.50    $false | (~spl7_2 | ~spl7_10 | ~spl7_27 | ~spl7_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f604,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl7_10 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.50  fof(f604,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k1_xboole_0) | (~spl7_2 | ~spl7_27 | ~spl7_78)),
% 0.21/0.50    inference(forward_demodulation,[],[f602,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl7_2 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.50  fof(f602,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,sK0)) | (~spl7_27 | ~spl7_78)),
% 0.21/0.50    inference(resolution,[],[f600,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) | ~spl7_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl7_27 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.50  fof(f600,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK2(k1_relat_1(sK1),sK0),X0) | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0))) ) | ~spl7_78),
% 0.21/0.50    inference(avatar_component_clause,[],[f599])).
% 0.21/0.50  fof(f599,plain,(
% 0.21/0.50    spl7_78 <=> ! [X0] : (~r2_hidden(sK2(k1_relat_1(sK1),sK0),X0) | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 0.21/0.50  fof(f601,plain,(
% 0.21/0.50    spl7_78 | ~spl7_1 | ~spl7_26 | ~spl7_44),
% 0.21/0.50    inference(avatar_split_clause,[],[f301,f292,f174,f49,f599])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl7_1 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    spl7_26 <=> ! [X1,X3,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    spl7_44 <=> r2_hidden(k4_tarski(sK2(k1_relat_1(sK1),sK0),sK4(sK1,sK2(k1_relat_1(sK1),sK0))),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK2(k1_relat_1(sK1),sK0),X0) | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0))) ) | (~spl7_1 | ~spl7_26 | ~spl7_44)),
% 0.21/0.50    inference(subsumption_resolution,[],[f298,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v1_relat_1(sK1) | ~spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f49])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0),X0) | r2_hidden(sK4(sK1,sK2(k1_relat_1(sK1),sK0)),k9_relat_1(sK1,X0))) ) | (~spl7_26 | ~spl7_44)),
% 0.21/0.50    inference(resolution,[],[f293,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) ) | ~spl7_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f174])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK2(k1_relat_1(sK1),sK0),sK4(sK1,sK2(k1_relat_1(sK1),sK0))),sK1) | ~spl7_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f292])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    spl7_44 | ~spl7_19 | ~spl7_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f206,f198,f125,f292])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl7_19 <=> ! [X0,X2] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl7_31 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK2(k1_relat_1(sK1),sK0),sK4(sK1,sK2(k1_relat_1(sK1),sK0))),sK1) | (~spl7_19 | ~spl7_31)),
% 0.21/0.50    inference(resolution,[],[f199,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)) ) | ~spl7_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | ~spl7_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f198])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl7_31 | spl7_3 | ~spl7_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f159,f93,f56,f198])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl7_3 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl7_11 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | (spl7_3 | ~spl7_11)),
% 0.21/0.50    inference(resolution,[],[f60,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) ) | ~spl7_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl7_27 | spl7_3 | ~spl7_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f158,f97,f56,f178])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl7_12 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) | (spl7_3 | ~spl7_12)),
% 0.21/0.50    inference(resolution,[],[f60,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) ) | ~spl7_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl7_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f174])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f42,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl7_2 | ~spl7_3 | ~spl7_22),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    $false | (spl7_2 | ~spl7_3 | ~spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f154,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_relat_1(sK1),sK0) | (spl7_2 | ~spl7_22)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0) | (spl7_2 | ~spl7_22)),
% 0.21/0.50    inference(superposition,[],[f59,f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,X1) | ~r1_xboole_0(k1_relat_1(sK1),X1)) ) | ~spl7_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl7_22 <=> ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,X1) | ~r1_xboole_0(k1_relat_1(sK1),X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f53])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl7_22 | ~spl7_1 | ~spl7_5 | ~spl7_15 | ~spl7_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f138,f130,f109,f67,f49,f145])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl7_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl7_15 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl7_20 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,X1) | ~r1_xboole_0(k1_relat_1(sK1),X1)) ) | (~spl7_1 | ~spl7_5 | ~spl7_15 | ~spl7_20)),
% 0.21/0.50    inference(forward_demodulation,[],[f137,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,X1) | ~r1_xboole_0(k1_relat_1(sK1),X1)) ) | (~spl7_1 | ~spl7_15 | ~spl7_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f136,f50])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,X1) | ~v1_relat_1(sK1) | ~r1_xboole_0(k1_relat_1(sK1),X1)) ) | (~spl7_15 | ~spl7_20)),
% 0.21/0.50    inference(superposition,[],[f110,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,X0) | ~r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl7_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f130])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl7_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl7_20 | ~spl7_1 | ~spl7_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f128,f113,f49,f130])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl7_16 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | (~spl7_1 | ~spl7_16)),
% 0.21/0.50    inference(resolution,[],[f114,f50])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl7_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f113])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl7_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f125])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl7_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f113])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl7_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f109])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl7_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f97])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl7_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f93])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl7_10 | ~spl7_6 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f86,f75,f71,f88])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl7_6 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl7_7 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(superposition,[],[f72,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f75])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f71])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl7_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f67])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~spl7_2 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f56,f53])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl7_2 | spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f56,f53])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (21714)------------------------------
% 0.21/0.50  % (21714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21714)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (21714)Memory used [KB]: 11001
% 0.21/0.50  % (21714)Time elapsed: 0.102 s
% 0.21/0.50  % (21714)------------------------------
% 0.21/0.50  % (21714)------------------------------
% 0.21/0.51  % (21704)Success in time 0.146 s
%------------------------------------------------------------------------------
