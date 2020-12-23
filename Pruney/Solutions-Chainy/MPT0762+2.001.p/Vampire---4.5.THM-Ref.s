%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 405 expanded)
%              Number of leaves         :   45 ( 195 expanded)
%              Depth                    :    8
%              Number of atoms          :  729 (1646 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f69,f73,f77,f81,f85,f89,f93,f97,f101,f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f162,f184,f193,f198,f205,f212,f219,f222,f227,f228,f233,f235,f236,f238,f239,f243,f245,f248,f251,f254,f257,f260,f263])).

fof(f263,plain,
    ( ~ spl1_1
    | ~ spl1_28
    | ~ spl1_18
    | spl1_32 ),
    inference(avatar_split_clause,[],[f261,f195,f127,f169,f57])).

fof(f57,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f169,plain,
    ( spl1_28
  <=> r1_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f127,plain,
    ( spl1_18
  <=> ! [X0] :
        ( v1_relat_2(X0)
        | ~ r1_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f195,plain,
    ( spl1_32
  <=> v1_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).

fof(f261,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_18
    | spl1_32 ),
    inference(resolution,[],[f197,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( v1_relat_2(X0)
        | ~ r1_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f197,plain,
    ( ~ v1_relat_2(sK0)
    | spl1_32 ),
    inference(avatar_component_clause,[],[f195])).

fof(f260,plain,
    ( ~ spl1_1
    | ~ spl1_30
    | ~ spl1_10
    | spl1_34 ),
    inference(avatar_split_clause,[],[f258,f209,f95,f177,f57])).

fof(f177,plain,
    ( spl1_30
  <=> r4_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f95,plain,
    ( spl1_10
  <=> ! [X0] :
        ( v4_relat_2(X0)
        | ~ r4_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f209,plain,
    ( spl1_34
  <=> v4_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).

fof(f258,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_10
    | spl1_34 ),
    inference(resolution,[],[f211,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( v4_relat_2(X0)
        | ~ r4_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f211,plain,
    ( ~ v4_relat_2(sK0)
    | spl1_34 ),
    inference(avatar_component_clause,[],[f209])).

fof(f257,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_23
    | spl1_29 ),
    inference(avatar_split_clause,[],[f256,f173,f147,f62,f57])).

fof(f62,plain,
    ( spl1_2
  <=> r2_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f147,plain,
    ( spl1_23
  <=> ! [X1,X0] :
        ( r1_wellord1(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f173,plain,
    ( spl1_29
  <=> r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_29])])).

fof(f256,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_23
    | spl1_29 ),
    inference(resolution,[],[f175,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( r1_wellord1(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f175,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | spl1_29 ),
    inference(avatar_component_clause,[],[f173])).

fof(f254,plain,
    ( ~ spl1_1
    | ~ spl1_29
    | ~ spl1_16
    | spl1_33 ),
    inference(avatar_split_clause,[],[f252,f202,f119,f173,f57])).

fof(f119,plain,
    ( spl1_16
  <=> ! [X0] :
        ( v1_wellord1(X0)
        | ~ r1_wellord1(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f202,plain,
    ( spl1_33
  <=> v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f252,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_16
    | spl1_33 ),
    inference(resolution,[],[f204,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( v1_wellord1(X0)
        | ~ r1_wellord1(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f119])).

fof(f204,plain,
    ( ~ v1_wellord1(sK0)
    | spl1_33 ),
    inference(avatar_component_clause,[],[f202])).

fof(f251,plain,
    ( ~ spl1_1
    | ~ spl1_31
    | ~ spl1_12
    | spl1_35 ),
    inference(avatar_split_clause,[],[f249,f216,f103,f181,f57])).

fof(f181,plain,
    ( spl1_31
  <=> r6_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f103,plain,
    ( spl1_12
  <=> ! [X0] :
        ( v6_relat_2(X0)
        | ~ r6_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f216,plain,
    ( spl1_35
  <=> v6_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f249,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_12
    | spl1_35 ),
    inference(resolution,[],[f218,f104])).

fof(f104,plain,
    ( ! [X0] :
        ( v6_relat_2(X0)
        | ~ r6_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f218,plain,
    ( ~ v6_relat_2(sK0)
    | spl1_35 ),
    inference(avatar_component_clause,[],[f216])).

fof(f248,plain,
    ( ~ spl1_1
    | ~ spl1_36
    | ~ spl1_14
    | spl1_27 ),
    inference(avatar_split_clause,[],[f246,f165,f111,f230,f57])).

fof(f230,plain,
    ( spl1_36
  <=> r8_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).

fof(f111,plain,
    ( spl1_14
  <=> ! [X0] :
        ( v8_relat_2(X0)
        | ~ r8_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f165,plain,
    ( spl1_27
  <=> v8_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f246,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_14
    | spl1_27 ),
    inference(resolution,[],[f167,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( v8_relat_2(X0)
        | ~ r8_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f167,plain,
    ( ~ v8_relat_2(sK0)
    | spl1_27 ),
    inference(avatar_component_clause,[],[f165])).

fof(f245,plain,
    ( ~ spl1_1
    | ~ spl1_32
    | ~ spl1_27
    | ~ spl1_34
    | ~ spl1_35
    | ~ spl1_33
    | spl1_3
    | ~ spl1_24 ),
    inference(avatar_split_clause,[],[f244,f151,f66,f202,f216,f209,f165,f195,f57])).

fof(f66,plain,
    ( spl1_3
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f151,plain,
    ( spl1_24
  <=> ! [X0] :
        ( v2_wellord1(X0)
        | ~ v1_wellord1(X0)
        | ~ v6_relat_2(X0)
        | ~ v4_relat_2(X0)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_2(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f244,plain,
    ( ~ v1_wellord1(sK0)
    | ~ v6_relat_2(sK0)
    | ~ v4_relat_2(sK0)
    | ~ v8_relat_2(sK0)
    | ~ v1_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3
    | ~ spl1_24 ),
    inference(resolution,[],[f67,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( v2_wellord1(X0)
        | ~ v1_wellord1(X0)
        | ~ v6_relat_2(X0)
        | ~ v4_relat_2(X0)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f151])).

fof(f67,plain,
    ( ~ v2_wellord1(sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f243,plain,
    ( ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f33,f66,f62])).

fof(f33,plain,
    ( ~ v2_wellord1(sK0)
    | ~ r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ v2_wellord1(sK0)
      | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
    & ( v2_wellord1(sK0)
      | r2_wellord1(sK0,k3_relat_1(sK0)) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( ~ v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) )
        & ( v2_wellord1(X0)
          | r2_wellord1(X0,k3_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ( ~ v2_wellord1(sK0)
        | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
      & ( v2_wellord1(sK0)
        | r2_wellord1(sK0,k3_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <~> v2_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( r2_wellord1(X0,k3_relat_1(X0))
        <=> v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

fof(f239,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_7
    | spl1_35 ),
    inference(avatar_split_clause,[],[f221,f216,f83,f66,f57])).

fof(f83,plain,
    ( spl1_7
  <=> ! [X0] :
        ( v6_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f221,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_7
    | spl1_35 ),
    inference(resolution,[],[f218,f84])).

fof(f84,plain,
    ( ! [X0] :
        ( v6_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f238,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_6
    | spl1_34 ),
    inference(avatar_split_clause,[],[f214,f209,f79,f66,f57])).

fof(f79,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v4_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f214,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_6
    | spl1_34 ),
    inference(resolution,[],[f211,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( v4_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f236,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_8
    | spl1_33 ),
    inference(avatar_split_clause,[],[f207,f202,f87,f66,f57])).

fof(f87,plain,
    ( spl1_8
  <=> ! [X0] :
        ( v1_wellord1(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f207,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_8
    | spl1_33 ),
    inference(resolution,[],[f204,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( v1_wellord1(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f235,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_19
    | spl1_28 ),
    inference(avatar_split_clause,[],[f188,f169,f131,f62,f57])).

fof(f131,plain,
    ( spl1_19
  <=> ! [X1,X0] :
        ( r1_relat_2(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f188,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_19
    | spl1_28 ),
    inference(resolution,[],[f171,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r1_relat_2(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f171,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | spl1_28 ),
    inference(avatar_component_clause,[],[f169])).

fof(f233,plain,
    ( ~ spl1_1
    | spl1_36
    | ~ spl1_2
    | ~ spl1_20 ),
    inference(avatar_split_clause,[],[f226,f135,f62,f230,f57])).

fof(f135,plain,
    ( spl1_20
  <=> ! [X1,X0] :
        ( r8_relat_2(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f226,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_20 ),
    inference(resolution,[],[f64,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r2_wellord1(X0,X1)
        | r8_relat_2(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f135])).

fof(f64,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f228,plain,
    ( ~ spl1_1
    | spl1_30
    | ~ spl1_2
    | ~ spl1_21 ),
    inference(avatar_split_clause,[],[f225,f139,f62,f177,f57])).

fof(f139,plain,
    ( spl1_21
  <=> ! [X1,X0] :
        ( r4_relat_2(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f225,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_21 ),
    inference(resolution,[],[f64,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ r2_wellord1(X0,X1)
        | r4_relat_2(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f139])).

fof(f227,plain,
    ( ~ spl1_1
    | spl1_31
    | ~ spl1_2
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f224,f143,f62,f181,f57])).

fof(f143,plain,
    ( spl1_22
  <=> ! [X1,X0] :
        ( r6_relat_2(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f224,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_22 ),
    inference(resolution,[],[f64,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r2_wellord1(X0,X1)
        | r6_relat_2(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f222,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | spl1_32 ),
    inference(avatar_split_clause,[],[f200,f195,f71,f66,f57])).

fof(f71,plain,
    ( spl1_4
  <=> ! [X0] :
        ( v1_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f200,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4
    | spl1_32 ),
    inference(resolution,[],[f197,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( v1_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f219,plain,
    ( ~ spl1_1
    | ~ spl1_35
    | ~ spl1_11
    | spl1_31 ),
    inference(avatar_split_clause,[],[f192,f181,f99,f216,f57])).

fof(f99,plain,
    ( spl1_11
  <=> ! [X0] :
        ( r6_relat_2(X0,k3_relat_1(X0))
        | ~ v6_relat_2(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f192,plain,
    ( ~ v6_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_11
    | spl1_31 ),
    inference(resolution,[],[f183,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( r6_relat_2(X0,k3_relat_1(X0))
        | ~ v6_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f183,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | spl1_31 ),
    inference(avatar_component_clause,[],[f181])).

fof(f212,plain,
    ( ~ spl1_1
    | ~ spl1_34
    | ~ spl1_9
    | spl1_30 ),
    inference(avatar_split_clause,[],[f191,f177,f91,f209,f57])).

fof(f91,plain,
    ( spl1_9
  <=> ! [X0] :
        ( r4_relat_2(X0,k3_relat_1(X0))
        | ~ v4_relat_2(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f191,plain,
    ( ~ v4_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_9
    | spl1_30 ),
    inference(resolution,[],[f179,f92])).

fof(f92,plain,
    ( ! [X0] :
        ( r4_relat_2(X0,k3_relat_1(X0))
        | ~ v4_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f179,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | spl1_30 ),
    inference(avatar_component_clause,[],[f177])).

fof(f205,plain,
    ( ~ spl1_1
    | ~ spl1_33
    | ~ spl1_15
    | spl1_29 ),
    inference(avatar_split_clause,[],[f189,f173,f115,f202,f57])).

fof(f115,plain,
    ( spl1_15
  <=> ! [X0] :
        ( r1_wellord1(X0,k3_relat_1(X0))
        | ~ v1_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f189,plain,
    ( ~ v1_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_15
    | spl1_29 ),
    inference(resolution,[],[f175,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( r1_wellord1(X0,k3_relat_1(X0))
        | ~ v1_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f198,plain,
    ( ~ spl1_1
    | ~ spl1_32
    | ~ spl1_17
    | spl1_28 ),
    inference(avatar_split_clause,[],[f187,f169,f123,f195,f57])).

fof(f123,plain,
    ( spl1_17
  <=> ! [X0] :
        ( r1_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_2(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f187,plain,
    ( ~ v1_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_17
    | spl1_28 ),
    inference(resolution,[],[f171,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( r1_relat_2(X0,k3_relat_1(X0))
        | ~ v1_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f193,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_5
    | spl1_27 ),
    inference(avatar_split_clause,[],[f186,f165,f75,f66,f57])).

fof(f75,plain,
    ( spl1_5
  <=> ! [X0] :
        ( v8_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f186,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_5
    | spl1_27 ),
    inference(resolution,[],[f167,f76])).

fof(f76,plain,
    ( ! [X0] :
        ( v8_relat_2(X0)
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f184,plain,
    ( ~ spl1_1
    | ~ spl1_27
    | spl1_2
    | ~ spl1_28
    | ~ spl1_29
    | ~ spl1_30
    | ~ spl1_31
    | ~ spl1_13
    | ~ spl1_26 ),
    inference(avatar_split_clause,[],[f163,f160,f107,f181,f177,f173,f169,f62,f165,f57])).

fof(f107,plain,
    ( spl1_13
  <=> ! [X0] :
        ( r8_relat_2(X0,k3_relat_1(X0))
        | ~ v8_relat_2(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f160,plain,
    ( spl1_26
  <=> ! [X0] :
        ( ~ r1_wellord1(sK0,X0)
        | ~ r6_relat_2(sK0,X0)
        | ~ r4_relat_2(sK0,X0)
        | ~ r8_relat_2(sK0,X0)
        | ~ r1_relat_2(sK0,X0)
        | r2_wellord1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f163,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v8_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_13
    | ~ spl1_26 ),
    inference(resolution,[],[f161,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( r8_relat_2(X0,k3_relat_1(X0))
        | ~ v8_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f107])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r8_relat_2(sK0,X0)
        | ~ r6_relat_2(sK0,X0)
        | ~ r4_relat_2(sK0,X0)
        | ~ r1_wellord1(sK0,X0)
        | ~ r1_relat_2(sK0,X0)
        | r2_wellord1(sK0,X0) )
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl1_26
    | ~ spl1_1
    | ~ spl1_25 ),
    inference(avatar_split_clause,[],[f158,f155,f57,f160])).

fof(f155,plain,
    ( spl1_25
  <=> ! [X1,X0] :
        ( r2_wellord1(X0,X1)
        | ~ r1_wellord1(X0,X1)
        | ~ r6_relat_2(X0,X1)
        | ~ r4_relat_2(X0,X1)
        | ~ r8_relat_2(X0,X1)
        | ~ r1_relat_2(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r1_wellord1(sK0,X0)
        | ~ r6_relat_2(sK0,X0)
        | ~ r4_relat_2(sK0,X0)
        | ~ r8_relat_2(sK0,X0)
        | ~ r1_relat_2(sK0,X0)
        | r2_wellord1(sK0,X0) )
    | ~ spl1_1
    | ~ spl1_25 ),
    inference(resolution,[],[f156,f59])).

fof(f59,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_wellord1(X0,X1)
        | ~ r6_relat_2(X0,X1)
        | ~ r4_relat_2(X0,X1)
        | ~ r8_relat_2(X0,X1)
        | ~ r1_relat_2(X0,X1)
        | r2_wellord1(X0,X1) )
    | ~ spl1_25 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,(
    spl1_25 ),
    inference(avatar_split_clause,[],[f55,f155])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_wellord1(X0,X1)
      | ~ r1_wellord1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(f153,plain,(
    spl1_24 ),
    inference(avatar_split_clause,[],[f49,f151])).

fof(f49,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f149,plain,(
    spl1_23 ),
    inference(avatar_split_clause,[],[f54,f147])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f145,plain,(
    spl1_22 ),
    inference(avatar_split_clause,[],[f53,f143])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f141,plain,(
    spl1_21 ),
    inference(avatar_split_clause,[],[f52,f139])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f137,plain,(
    spl1_20 ),
    inference(avatar_split_clause,[],[f51,f135])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f133,plain,(
    spl1_19 ),
    inference(avatar_split_clause,[],[f50,f131])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f129,plain,(
    spl1_18 ),
    inference(avatar_split_clause,[],[f43,f127])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

fof(f125,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f42,f123])).

fof(f42,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f121,plain,(
    spl1_16 ),
    inference(avatar_split_clause,[],[f41,f119])).

fof(f41,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ~ r1_wellord1(X0,k3_relat_1(X0)) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

fof(f117,plain,(
    spl1_15 ),
    inference(avatar_split_clause,[],[f40,f115])).

fof(f40,plain,(
    ! [X0] :
      ( r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f113,plain,(
    spl1_14 ),
    inference(avatar_split_clause,[],[f39,f111])).

fof(f39,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(f109,plain,(
    spl1_13 ),
    inference(avatar_split_clause,[],[f38,f107])).

fof(f38,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f105,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f37,f103])).

fof(f37,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

fof(f101,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f36,f99])).

fof(f36,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f35,f95])).

fof(f35,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

fof(f93,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f34,f91])).

fof(f34,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f48,f87])).

fof(f48,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f47,f83])).

fof(f47,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f46,f79])).

fof(f46,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f44,f71])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,
    ( spl1_2
    | spl1_3 ),
    inference(avatar_split_clause,[],[f32,f66,f62])).

fof(f32,plain,
    ( v2_wellord1(sK0)
    | r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (25219)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.46  % (25228)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.47  % (25228)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (25221)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f264,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f60,f69,f73,f77,f81,f85,f89,f93,f97,f101,f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f162,f184,f193,f198,f205,f212,f219,f222,f227,f228,f233,f235,f236,f238,f239,f243,f245,f248,f251,f254,f257,f260,f263])).
% 0.22/0.47  fof(f263,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_28 | ~spl1_18 | spl1_32),
% 0.22/0.47    inference(avatar_split_clause,[],[f261,f195,f127,f169,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl1_1 <=> v1_relat_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.47  fof(f169,plain,(
% 0.22/0.47    spl1_28 <=> r1_relat_2(sK0,k3_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl1_18 <=> ! [X0] : (v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.22/0.47  fof(f195,plain,(
% 0.22/0.47    spl1_32 <=> v1_relat_2(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).
% 0.22/0.47  fof(f261,plain,(
% 0.22/0.47    ~r1_relat_2(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_18 | spl1_32)),
% 0.22/0.47    inference(resolution,[],[f197,f128])).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f127])).
% 0.22/0.47  fof(f197,plain,(
% 0.22/0.47    ~v1_relat_2(sK0) | spl1_32),
% 0.22/0.47    inference(avatar_component_clause,[],[f195])).
% 0.22/0.47  fof(f260,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_30 | ~spl1_10 | spl1_34),
% 0.22/0.47    inference(avatar_split_clause,[],[f258,f209,f95,f177,f57])).
% 0.22/0.47  fof(f177,plain,(
% 0.22/0.47    spl1_30 <=> r4_relat_2(sK0,k3_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    spl1_10 <=> ! [X0] : (v4_relat_2(X0) | ~r4_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.47  fof(f209,plain,(
% 0.22/0.47    spl1_34 <=> v4_relat_2(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).
% 0.22/0.47  fof(f258,plain,(
% 0.22/0.47    ~r4_relat_2(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_10 | spl1_34)),
% 0.22/0.47    inference(resolution,[],[f211,f96])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    ( ! [X0] : (v4_relat_2(X0) | ~r4_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f95])).
% 0.22/0.47  fof(f211,plain,(
% 0.22/0.47    ~v4_relat_2(sK0) | spl1_34),
% 0.22/0.47    inference(avatar_component_clause,[],[f209])).
% 0.22/0.47  fof(f257,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_2 | ~spl1_23 | spl1_29),
% 0.22/0.47    inference(avatar_split_clause,[],[f256,f173,f147,f62,f57])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl1_2 <=> r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.47  fof(f147,plain,(
% 0.22/0.47    spl1_23 <=> ! [X1,X0] : (r1_wellord1(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.22/0.47  fof(f173,plain,(
% 0.22/0.47    spl1_29 <=> r1_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_29])])).
% 0.22/0.47  fof(f256,plain,(
% 0.22/0.47    ~r2_wellord1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_23 | spl1_29)),
% 0.22/0.47    inference(resolution,[],[f175,f148])).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_wellord1(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) ) | ~spl1_23),
% 0.22/0.47    inference(avatar_component_clause,[],[f147])).
% 0.22/0.47  fof(f175,plain,(
% 0.22/0.47    ~r1_wellord1(sK0,k3_relat_1(sK0)) | spl1_29),
% 0.22/0.47    inference(avatar_component_clause,[],[f173])).
% 0.22/0.47  fof(f254,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_29 | ~spl1_16 | spl1_33),
% 0.22/0.47    inference(avatar_split_clause,[],[f252,f202,f119,f173,f57])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    spl1_16 <=> ! [X0] : (v1_wellord1(X0) | ~r1_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.22/0.47  fof(f202,plain,(
% 0.22/0.47    spl1_33 <=> v1_wellord1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.22/0.47  fof(f252,plain,(
% 0.22/0.47    ~r1_wellord1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_16 | spl1_33)),
% 0.22/0.47    inference(resolution,[],[f204,f120])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    ( ! [X0] : (v1_wellord1(X0) | ~r1_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f119])).
% 0.22/0.47  fof(f204,plain,(
% 0.22/0.47    ~v1_wellord1(sK0) | spl1_33),
% 0.22/0.47    inference(avatar_component_clause,[],[f202])).
% 0.22/0.47  fof(f251,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_31 | ~spl1_12 | spl1_35),
% 0.22/0.47    inference(avatar_split_clause,[],[f249,f216,f103,f181,f57])).
% 0.22/0.47  fof(f181,plain,(
% 0.22/0.47    spl1_31 <=> r6_relat_2(sK0,k3_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    spl1_12 <=> ! [X0] : (v6_relat_2(X0) | ~r6_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.47  fof(f216,plain,(
% 0.22/0.47    spl1_35 <=> v6_relat_2(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.22/0.47  fof(f249,plain,(
% 0.22/0.47    ~r6_relat_2(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_12 | spl1_35)),
% 0.22/0.47    inference(resolution,[],[f218,f104])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    ( ! [X0] : (v6_relat_2(X0) | ~r6_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f103])).
% 0.22/0.47  fof(f218,plain,(
% 0.22/0.47    ~v6_relat_2(sK0) | spl1_35),
% 0.22/0.47    inference(avatar_component_clause,[],[f216])).
% 0.22/0.47  fof(f248,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_36 | ~spl1_14 | spl1_27),
% 0.22/0.47    inference(avatar_split_clause,[],[f246,f165,f111,f230,f57])).
% 0.22/0.47  fof(f230,plain,(
% 0.22/0.47    spl1_36 <=> r8_relat_2(sK0,k3_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    spl1_14 <=> ! [X0] : (v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.47  fof(f165,plain,(
% 0.22/0.47    spl1_27 <=> v8_relat_2(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.22/0.47  fof(f246,plain,(
% 0.22/0.47    ~r8_relat_2(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_14 | spl1_27)),
% 0.22/0.47    inference(resolution,[],[f167,f112])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ( ! [X0] : (v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f111])).
% 0.22/0.47  fof(f167,plain,(
% 0.22/0.47    ~v8_relat_2(sK0) | spl1_27),
% 0.22/0.47    inference(avatar_component_clause,[],[f165])).
% 0.22/0.47  fof(f245,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_32 | ~spl1_27 | ~spl1_34 | ~spl1_35 | ~spl1_33 | spl1_3 | ~spl1_24),
% 0.22/0.47    inference(avatar_split_clause,[],[f244,f151,f66,f202,f216,f209,f165,f195,f57])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl1_3 <=> v2_wellord1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    spl1_24 <=> ! [X0] : (v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 0.22/0.47  fof(f244,plain,(
% 0.22/0.47    ~v1_wellord1(sK0) | ~v6_relat_2(sK0) | ~v4_relat_2(sK0) | ~v8_relat_2(sK0) | ~v1_relat_2(sK0) | ~v1_relat_1(sK0) | (spl1_3 | ~spl1_24)),
% 0.22/0.47    inference(resolution,[],[f67,f152])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    ( ! [X0] : (v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) ) | ~spl1_24),
% 0.22/0.47    inference(avatar_component_clause,[],[f151])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ~v2_wellord1(sK0) | spl1_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f66])).
% 0.22/0.47  fof(f243,plain,(
% 0.22/0.47    ~spl1_2 | ~spl1_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f33,f66,f62])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ~v2_wellord1(sK0) | ~r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    (~v2_wellord1(sK0) | ~r2_wellord1(sK0,k3_relat_1(sK0))) & (v2_wellord1(sK0) | r2_wellord1(sK0,k3_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ? [X0] : ((~v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0))) & (v2_wellord1(X0) | r2_wellord1(X0,k3_relat_1(X0))) & v1_relat_1(X0)) => ((~v2_wellord1(sK0) | ~r2_wellord1(sK0,k3_relat_1(sK0))) & (v2_wellord1(sK0) | r2_wellord1(sK0,k3_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ? [X0] : ((~v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0))) & (v2_wellord1(X0) | r2_wellord1(X0,k3_relat_1(X0))) & v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X0] : (((~v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0))) & (v2_wellord1(X0) | r2_wellord1(X0,k3_relat_1(X0)))) & v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0] : ((r2_wellord1(X0,k3_relat_1(X0)) <~> v2_wellord1(X0)) & v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).
% 0.22/0.47  fof(f239,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_3 | ~spl1_7 | spl1_35),
% 0.22/0.47    inference(avatar_split_clause,[],[f221,f216,f83,f66,f57])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    spl1_7 <=> ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.47  fof(f221,plain,(
% 0.22/0.47    ~v2_wellord1(sK0) | ~v1_relat_1(sK0) | (~spl1_7 | spl1_35)),
% 0.22/0.47    inference(resolution,[],[f218,f84])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) ) | ~spl1_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f83])).
% 0.22/0.47  fof(f238,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_3 | ~spl1_6 | spl1_34),
% 0.22/0.47    inference(avatar_split_clause,[],[f214,f209,f79,f66,f57])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    spl1_6 <=> ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.47  fof(f214,plain,(
% 0.22/0.47    ~v2_wellord1(sK0) | ~v1_relat_1(sK0) | (~spl1_6 | spl1_34)),
% 0.22/0.47    inference(resolution,[],[f211,f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) ) | ~spl1_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f79])).
% 0.22/0.47  fof(f236,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_3 | ~spl1_8 | spl1_33),
% 0.22/0.47    inference(avatar_split_clause,[],[f207,f202,f87,f66,f57])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    spl1_8 <=> ! [X0] : (v1_wellord1(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.47  fof(f207,plain,(
% 0.22/0.47    ~v2_wellord1(sK0) | ~v1_relat_1(sK0) | (~spl1_8 | spl1_33)),
% 0.22/0.47    inference(resolution,[],[f204,f88])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    ( ! [X0] : (v1_wellord1(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f87])).
% 0.22/0.47  fof(f235,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_2 | ~spl1_19 | spl1_28),
% 0.22/0.47    inference(avatar_split_clause,[],[f188,f169,f131,f62,f57])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    spl1_19 <=> ! [X1,X0] : (r1_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    ~r2_wellord1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_19 | spl1_28)),
% 0.22/0.47    inference(resolution,[],[f171,f132])).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) ) | ~spl1_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f131])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    ~r1_relat_2(sK0,k3_relat_1(sK0)) | spl1_28),
% 0.22/0.47    inference(avatar_component_clause,[],[f169])).
% 0.22/0.47  fof(f233,plain,(
% 0.22/0.47    ~spl1_1 | spl1_36 | ~spl1_2 | ~spl1_20),
% 0.22/0.47    inference(avatar_split_clause,[],[f226,f135,f62,f230,f57])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    spl1_20 <=> ! [X1,X0] : (r8_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.22/0.47  fof(f226,plain,(
% 0.22/0.47    r8_relat_2(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_20)),
% 0.22/0.47    inference(resolution,[],[f64,f136])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) ) | ~spl1_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f135])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    r2_wellord1(sK0,k3_relat_1(sK0)) | ~spl1_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f228,plain,(
% 0.22/0.47    ~spl1_1 | spl1_30 | ~spl1_2 | ~spl1_21),
% 0.22/0.47    inference(avatar_split_clause,[],[f225,f139,f62,f177,f57])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    spl1_21 <=> ! [X1,X0] : (r4_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.22/0.47  fof(f225,plain,(
% 0.22/0.47    r4_relat_2(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_21)),
% 0.22/0.47    inference(resolution,[],[f64,f140])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) ) | ~spl1_21),
% 0.22/0.47    inference(avatar_component_clause,[],[f139])).
% 0.22/0.47  fof(f227,plain,(
% 0.22/0.47    ~spl1_1 | spl1_31 | ~spl1_2 | ~spl1_22),
% 0.22/0.47    inference(avatar_split_clause,[],[f224,f143,f62,f181,f57])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    spl1_22 <=> ! [X1,X0] : (r6_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.22/0.47  fof(f224,plain,(
% 0.22/0.47    r6_relat_2(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_22)),
% 0.22/0.47    inference(resolution,[],[f64,f144])).
% 0.22/0.47  fof(f144,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r6_relat_2(X0,X1) | ~v1_relat_1(X0)) ) | ~spl1_22),
% 0.22/0.47    inference(avatar_component_clause,[],[f143])).
% 0.22/0.47  fof(f222,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_3 | ~spl1_4 | spl1_32),
% 0.22/0.47    inference(avatar_split_clause,[],[f200,f195,f71,f66,f57])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl1_4 <=> ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.47  fof(f200,plain,(
% 0.22/0.47    ~v2_wellord1(sK0) | ~v1_relat_1(sK0) | (~spl1_4 | spl1_32)),
% 0.22/0.47    inference(resolution,[],[f197,f72])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f71])).
% 0.22/0.47  fof(f219,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_35 | ~spl1_11 | spl1_31),
% 0.22/0.47    inference(avatar_split_clause,[],[f192,f181,f99,f216,f57])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl1_11 <=> ! [X0] : (r6_relat_2(X0,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.47  fof(f192,plain,(
% 0.22/0.47    ~v6_relat_2(sK0) | ~v1_relat_1(sK0) | (~spl1_11 | spl1_31)),
% 0.22/0.47    inference(resolution,[],[f183,f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    ( ! [X0] : (r6_relat_2(X0,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) ) | ~spl1_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f99])).
% 0.22/0.47  fof(f183,plain,(
% 0.22/0.47    ~r6_relat_2(sK0,k3_relat_1(sK0)) | spl1_31),
% 0.22/0.47    inference(avatar_component_clause,[],[f181])).
% 0.22/0.47  fof(f212,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_34 | ~spl1_9 | spl1_30),
% 0.22/0.47    inference(avatar_split_clause,[],[f191,f177,f91,f209,f57])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    spl1_9 <=> ! [X0] : (r4_relat_2(X0,k3_relat_1(X0)) | ~v4_relat_2(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.47  fof(f191,plain,(
% 0.22/0.47    ~v4_relat_2(sK0) | ~v1_relat_1(sK0) | (~spl1_9 | spl1_30)),
% 0.22/0.47    inference(resolution,[],[f179,f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ( ! [X0] : (r4_relat_2(X0,k3_relat_1(X0)) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) ) | ~spl1_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f91])).
% 0.22/0.47  fof(f179,plain,(
% 0.22/0.47    ~r4_relat_2(sK0,k3_relat_1(sK0)) | spl1_30),
% 0.22/0.47    inference(avatar_component_clause,[],[f177])).
% 0.22/0.47  fof(f205,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_33 | ~spl1_15 | spl1_29),
% 0.22/0.47    inference(avatar_split_clause,[],[f189,f173,f115,f202,f57])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    spl1_15 <=> ! [X0] : (r1_wellord1(X0,k3_relat_1(X0)) | ~v1_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.22/0.47  fof(f189,plain,(
% 0.22/0.47    ~v1_wellord1(sK0) | ~v1_relat_1(sK0) | (~spl1_15 | spl1_29)),
% 0.22/0.47    inference(resolution,[],[f175,f116])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ( ! [X0] : (r1_wellord1(X0,k3_relat_1(X0)) | ~v1_wellord1(X0) | ~v1_relat_1(X0)) ) | ~spl1_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f115])).
% 0.22/0.47  fof(f198,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_32 | ~spl1_17 | spl1_28),
% 0.22/0.47    inference(avatar_split_clause,[],[f187,f169,f123,f195,f57])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    spl1_17 <=> ! [X0] : (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.22/0.47  fof(f187,plain,(
% 0.22/0.47    ~v1_relat_2(sK0) | ~v1_relat_1(sK0) | (~spl1_17 | spl1_28)),
% 0.22/0.47    inference(resolution,[],[f171,f124])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    ( ! [X0] : (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) ) | ~spl1_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f123])).
% 0.22/0.47  fof(f193,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_3 | ~spl1_5 | spl1_27),
% 0.22/0.47    inference(avatar_split_clause,[],[f186,f165,f75,f66,f57])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    spl1_5 <=> ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    ~v2_wellord1(sK0) | ~v1_relat_1(sK0) | (~spl1_5 | spl1_27)),
% 0.22/0.47    inference(resolution,[],[f167,f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) ) | ~spl1_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f75])).
% 0.22/0.47  fof(f184,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_27 | spl1_2 | ~spl1_28 | ~spl1_29 | ~spl1_30 | ~spl1_31 | ~spl1_13 | ~spl1_26),
% 0.22/0.47    inference(avatar_split_clause,[],[f163,f160,f107,f181,f177,f173,f169,f62,f165,f57])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    spl1_13 <=> ! [X0] : (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    spl1_26 <=> ! [X0] : (~r1_wellord1(sK0,X0) | ~r6_relat_2(sK0,X0) | ~r4_relat_2(sK0,X0) | ~r8_relat_2(sK0,X0) | ~r1_relat_2(sK0,X0) | r2_wellord1(sK0,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.22/0.47  fof(f163,plain,(
% 0.22/0.47    ~r6_relat_2(sK0,k3_relat_1(sK0)) | ~r4_relat_2(sK0,k3_relat_1(sK0)) | ~r1_wellord1(sK0,k3_relat_1(sK0)) | ~r1_relat_2(sK0,k3_relat_1(sK0)) | r2_wellord1(sK0,k3_relat_1(sK0)) | ~v8_relat_2(sK0) | ~v1_relat_1(sK0) | (~spl1_13 | ~spl1_26)),
% 0.22/0.47    inference(resolution,[],[f161,f108])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    ( ! [X0] : (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) ) | ~spl1_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f107])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    ( ! [X0] : (~r8_relat_2(sK0,X0) | ~r6_relat_2(sK0,X0) | ~r4_relat_2(sK0,X0) | ~r1_wellord1(sK0,X0) | ~r1_relat_2(sK0,X0) | r2_wellord1(sK0,X0)) ) | ~spl1_26),
% 0.22/0.47    inference(avatar_component_clause,[],[f160])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    spl1_26 | ~spl1_1 | ~spl1_25),
% 0.22/0.47    inference(avatar_split_clause,[],[f158,f155,f57,f160])).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    spl1_25 <=> ! [X1,X0] : (r2_wellord1(X0,X1) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_wellord1(sK0,X0) | ~r6_relat_2(sK0,X0) | ~r4_relat_2(sK0,X0) | ~r8_relat_2(sK0,X0) | ~r1_relat_2(sK0,X0) | r2_wellord1(sK0,X0)) ) | (~spl1_1 | ~spl1_25)),
% 0.22/0.47    inference(resolution,[],[f156,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    v1_relat_1(sK0) | ~spl1_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f57])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1) | r2_wellord1(X0,X1)) ) | ~spl1_25),
% 0.22/0.47    inference(avatar_component_clause,[],[f155])).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    spl1_25),
% 0.22/0.47    inference(avatar_split_clause,[],[f55,f155])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_wellord1(X0,X1) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((r2_wellord1(X0,X1) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1)) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r2_wellord1(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((r2_wellord1(X0,X1) | (~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1))) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r2_wellord1(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    spl1_24),
% 0.22/0.47    inference(avatar_split_clause,[],[f49,f151])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0] : (v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    spl1_23),
% 0.22/0.47    inference(avatar_split_clause,[],[f54,f147])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_wellord1(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f145,plain,(
% 0.22/0.47    spl1_22),
% 0.22/0.47    inference(avatar_split_clause,[],[f53,f143])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r6_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f141,plain,(
% 0.22/0.47    spl1_21),
% 0.22/0.47    inference(avatar_split_clause,[],[f52,f139])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r4_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    spl1_20),
% 0.22/0.47    inference(avatar_split_clause,[],[f51,f135])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r8_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    spl1_19),
% 0.22/0.47    inference(avatar_split_clause,[],[f50,f131])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    spl1_18),
% 0.22/0.47    inference(avatar_split_clause,[],[f43,f127])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0] : (((v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0))) & (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : ((v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    spl1_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f42,f123])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0] : (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    spl1_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f41,f119])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0] : (v1_wellord1(X0) | ~r1_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0] : (((v1_wellord1(X0) | ~r1_wellord1(X0,k3_relat_1(X0))) & (r1_wellord1(X0,k3_relat_1(X0)) | ~v1_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : ((v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => (v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl1_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f40,f115])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0] : (r1_wellord1(X0,k3_relat_1(X0)) | ~v1_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    spl1_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f111])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0] : (v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0] : (((v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0))) & (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : ((v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    spl1_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f38,f107])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0] : (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl1_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f37,f103])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (v6_relat_2(X0) | ~r6_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0] : (((v6_relat_2(X0) | ~r6_relat_2(X0,k3_relat_1(X0))) & (r6_relat_2(X0,k3_relat_1(X0)) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : ((v6_relat_2(X0) <=> r6_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> r6_relat_2(X0,k3_relat_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl1_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f36,f99])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0] : (r6_relat_2(X0,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    spl1_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f35,f95])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0] : (v4_relat_2(X0) | ~r4_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : (((v4_relat_2(X0) | ~r4_relat_2(X0,k3_relat_1(X0))) & (r4_relat_2(X0,k3_relat_1(X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : ((v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    spl1_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f91])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0] : (r4_relat_2(X0,k3_relat_1(X0)) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    spl1_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f48,f87])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0] : (v1_wellord1(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    spl1_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f47,f83])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl1_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f46,f79])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl1_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f45,f75])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    spl1_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f44,f71])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl1_2 | spl1_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f32,f66,f62])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    v2_wellord1(sK0) | r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl1_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f31,f57])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    v1_relat_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (25228)------------------------------
% 0.22/0.47  % (25228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (25228)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (25228)Memory used [KB]: 5500
% 0.22/0.47  % (25228)Time elapsed: 0.054 s
% 0.22/0.47  % (25228)------------------------------
% 0.22/0.47  % (25228)------------------------------
% 0.22/0.48  % (25211)Success in time 0.115 s
%------------------------------------------------------------------------------
