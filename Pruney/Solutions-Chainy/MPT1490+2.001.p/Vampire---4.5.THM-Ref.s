%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  307 ( 796 expanded)
%              Number of leaves         :   61 ( 362 expanded)
%              Depth                    :   16
%              Number of atoms          : 1406 (3266 expanded)
%              Number of equality atoms :   34 (  85 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f114,f119,f124,f129,f134,f139,f152,f199,f201,f202,f236,f242,f252,f257,f262,f297,f325,f330,f357,f363,f400,f405,f410,f491,f522,f527,f532,f582,f591,f596,f601,f628,f636,f709,f715,f730,f790,f815,f818,f831,f888,f1000,f1006])).

fof(f1006,plain,
    ( ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_46
    | ~ spl13_48
    | spl13_59
    | ~ spl13_89 ),
    inference(avatar_contradiction_clause,[],[f1005])).

fof(f1005,plain,
    ( $false
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_46
    | ~ spl13_48
    | spl13_59
    | ~ spl13_89 ),
    inference(subsumption_resolution,[],[f1004,f617])).

fof(f617,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | spl13_59 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl13_59
  <=> r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_59])])).

fof(f1004,plain,
    ( r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_89 ),
    inference(forward_demodulation,[],[f1003,f521])).

fof(f521,plain,
    ( sK11(sK9,sK8,sK7) = k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl13_46
  <=> sK11(sK9,sK8,sK7) = k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f1003,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7))),sK9)
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_48
    | ~ spl13_89 ),
    inference(forward_demodulation,[],[f1001,f531])).

fof(f531,plain,
    ( sK9 = k7_lattices(sK8,k7_lattices(sK8,sK9))
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl13_48
  <=> sK9 = k7_lattices(sK8,k7_lattices(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f1001,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7))),k7_lattices(sK8,k7_lattices(sK8,sK9)))
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_89 ),
    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f329,f324,f991,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              | ~ r3_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              | ~ r3_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

fof(f991,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ spl13_89 ),
    inference(avatar_component_clause,[],[f989])).

fof(f989,plain,
    ( spl13_89
  <=> r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_89])])).

fof(f324,plain,
    ( m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8))
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f322])).

% (14248)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f322,plain,
    ( spl13_25
  <=> m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f329,plain,
    ( m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8))
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl13_26
  <=> m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f123,plain,
    ( l3_lattices(sK8)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl13_4
  <=> l3_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f128,plain,
    ( v17_lattices(sK8)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f126])).

% (14249)Refutation not found, incomplete strategy% (14249)------------------------------
% (14249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f126,plain,
    ( spl13_5
  <=> v17_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

% (14249)Termination reason: Refutation not found, incomplete strategy

% (14249)Memory used [KB]: 10618
% (14249)Time elapsed: 0.104 s
% (14249)------------------------------
% (14249)------------------------------
fof(f133,plain,
    ( v10_lattices(sK8)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl13_6
  <=> v10_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f138,plain,
    ( ~ v2_struct_0(sK8)
    | spl13_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl13_7
  <=> v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f1000,plain,
    ( spl13_89
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_78 ),
    inference(avatar_split_clause,[],[f999,f885,f327,f322,f183,f173,f168,f136,f121,f989])).

fof(f168,plain,
    ( spl13_9
  <=> v9_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f173,plain,
    ( spl13_10
  <=> v8_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f183,plain,
    ( spl13_12
  <=> v6_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f885,plain,
    ( spl13_78
  <=> r1_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f999,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f998,f138])).

fof(f998,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f997,f185])).

fof(f185,plain,
    ( v6_lattices(sK8)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f997,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f996,f175])).

fof(f175,plain,
    ( v8_lattices(sK8)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f173])).

fof(f996,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f995,f170])).

fof(f170,plain,
    ( v9_lattices(sK8)
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f995,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f994,f123])).

fof(f994,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_25
    | ~ spl13_26
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f993,f329])).

fof(f993,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_25
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f987,f324])).

fof(f987,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8))
    | ~ m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_78 ),
    inference(resolution,[],[f887,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f887,plain,
    ( r1_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ spl13_78 ),
    inference(avatar_component_clause,[],[f885])).

fof(f888,plain,
    ( spl13_78
    | ~ spl13_24
    | ~ spl13_25
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f874,f360,f322,f308,f885])).

fof(f308,plain,
    ( spl13_24
  <=> r2_hidden(k7_lattices(sK8,sK11(sK9,sK8,sK7)),a_2_0_lattice3(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f360,plain,
    ( spl13_30
  <=> sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f874,plain,
    ( r1_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ spl13_24
    | ~ spl13_25
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f361,f324,f309,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK10(X0,X1,X2))
          & r2_hidden(sK10(X0,X1,X2),X2)
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK10(X0,X1,X2))
        & r2_hidden(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f309,plain,
    ( r2_hidden(k7_lattices(sK8,sK11(sK9,sK8,sK7)),a_2_0_lattice3(sK7,sK8))
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f308])).

fof(f361,plain,
    ( sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f360])).

fof(f831,plain,
    ( ~ spl13_2
    | ~ spl13_27
    | spl13_30 ),
    inference(avatar_split_clause,[],[f393,f360,f338,f110])).

fof(f110,plain,
    ( spl13_2
  <=> r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f338,plain,
    ( spl13_27
  <=> sP2(sK8,k7_lattices(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f393,plain,
    ( ~ r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
    | ~ spl13_27
    | spl13_30 ),
    inference(unit_resulting_resolution,[],[f340,f362,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP1(X1,X0,X2) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f362,plain,
    ( ~ sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))
    | spl13_30 ),
    inference(avatar_component_clause,[],[f360])).

fof(f340,plain,
    ( sP2(sK8,k7_lattices(sK8,sK9))
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f338])).

fof(f818,plain,
    ( ~ spl13_23
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | spl13_24 ),
    inference(avatar_split_clause,[],[f312,f308,f136,f131,f126,f121,f294])).

fof(f294,plain,
    ( spl13_23
  <=> sP5(sK7,k7_lattices(sK8,sK11(sK9,sK8,sK7)),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

% (14258)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f312,plain,
    ( ~ sP5(sK7,k7_lattices(sK8,sK11(sK9,sK8,sK7)),sK8)
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | spl13_24 ),
    inference(unit_resulting_resolution,[],[f285,f310,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,a_2_0_lattice3(X2,X0))
      | ~ sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,a_2_0_lattice3(X2,X0))
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | ~ r2_hidden(X1,a_2_0_lattice3(X2,X0)) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ~ sP5(X1,X0,X2) )
        & ( sP5(X1,X0,X2)
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ sP6(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> sP5(X1,X0,X2) )
      | ~ sP6(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f310,plain,
    ( ~ r2_hidden(k7_lattices(sK8,sK11(sK9,sK8,sK7)),a_2_0_lattice3(sK7,sK8))
    | spl13_24 ),
    inference(avatar_component_clause,[],[f308])).

fof(f285,plain,
    ( ! [X0,X1] : sP6(sK8,X0,X1)
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7 ),
    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0,X1)
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP6(X2,X0,X1)
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(definition_folding,[],[f28,f38,f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & k7_lattices(X2,X3) = X0
          & m1_subset_1(X3,u1_struct_0(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X2)
        & v17_lattices(X2)
        & v10_lattices(X2)
        & ~ v2_struct_0(X2) )
     => ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).

fof(f815,plain,
    ( spl13_17
    | ~ spl13_1
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f299,f230,f106,f239])).

fof(f239,plain,
    ( spl13_17
  <=> sP3(sK9,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f106,plain,
    ( spl13_1
  <=> r4_lattice3(sK8,sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f230,plain,
    ( spl13_16
  <=> sP4(sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

% (14260)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (14255)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f299,plain,
    ( sP3(sK9,sK8,sK7)
    | ~ spl13_1
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f232,f107,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP3(X1,X0,X2) )
          & ( sP3(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f107,plain,
    ( r4_lattice3(sK8,sK9,sK7)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f232,plain,
    ( sP4(sK8,sK9)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f230])).

fof(f790,plain,
    ( ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_45
    | ~ spl13_47
    | spl13_58
    | ~ spl13_67 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_45
    | ~ spl13_47
    | spl13_58
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f788,f612])).

fof(f612,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | spl13_58 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl13_58
  <=> r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f788,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_45
    | ~ spl13_47
    | ~ spl13_67 ),
    inference(forward_demodulation,[],[f777,f526])).

fof(f526,plain,
    ( sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))))
    | ~ spl13_47 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl13_47
  <=> sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_47])])).

fof(f777,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))))
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_45
    | ~ spl13_67 ),
    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f490,f729,f118,f79])).

fof(f118,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl13_3
  <=> m1_subset_1(sK9,u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f729,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),sK9)
    | ~ spl13_67 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl13_67
  <=> r3_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_67])])).

fof(f490,plain,
    ( m1_subset_1(k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),u1_struct_0(sK8))
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl13_45
  <=> m1_subset_1(k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f730,plain,
    ( spl13_67
    | ~ spl13_65
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f722,f712,f706,f727])).

fof(f706,plain,
    ( spl13_65
  <=> k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) = sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).

fof(f712,plain,
    ( spl13_66
  <=> r3_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f722,plain,
    ( r3_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),sK9)
    | ~ spl13_65
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f714,f708])).

fof(f708,plain,
    ( k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) = sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)
    | ~ spl13_65 ),
    inference(avatar_component_clause,[],[f706])).

fof(f714,plain,
    ( r3_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK9)
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f712])).

fof(f715,plain,
    ( spl13_66
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_17
    | ~ spl13_55
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f677,f593,f588,f239,f183,f173,f168,f136,f121,f116,f712])).

fof(f588,plain,
    ( spl13_55
  <=> r2_hidden(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f593,plain,
    ( spl13_56
  <=> m1_subset_1(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f677,plain,
    ( r3_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK9)
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_17
    | ~ spl13_55
    | ~ spl13_56 ),
    inference(unit_resulting_resolution,[],[f590,f595,f674])).

fof(f674,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f673,f138])).

fof(f673,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | v2_struct_0(sK8)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f672,f185])).

fof(f672,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ v6_lattices(sK8)
        | v2_struct_0(sK8)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f671,f175])).

fof(f671,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ v8_lattices(sK8)
        | ~ v6_lattices(sK8)
        | v2_struct_0(sK8)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f670,f170])).

fof(f670,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ v9_lattices(sK8)
        | ~ v8_lattices(sK8)
        | ~ v6_lattices(sK8)
        | v2_struct_0(sK8)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f669,f123])).

fof(f669,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ l3_lattices(sK8)
        | ~ v9_lattices(sK8)
        | ~ v8_lattices(sK8)
        | ~ v6_lattices(sK8)
        | v2_struct_0(sK8)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_3
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f668,f118])).

fof(f668,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(sK9,u1_struct_0(sK8))
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ l3_lattices(sK8)
        | ~ v9_lattices(sK8)
        | ~ v8_lattices(sK8)
        | ~ v6_lattices(sK8)
        | v2_struct_0(sK8)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_17 ),
    inference(duplicate_literal_removal,[],[f665])).

fof(f665,plain,
    ( ! [X0] :
        ( r3_lattices(sK8,X0,sK9)
        | ~ m1_subset_1(sK9,u1_struct_0(sK8))
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ l3_lattices(sK8)
        | ~ v9_lattices(sK8)
        | ~ v8_lattices(sK8)
        | ~ v6_lattices(sK8)
        | v2_struct_0(sK8)
        | ~ m1_subset_1(X0,u1_struct_0(sK8))
        | ~ r2_hidden(X0,sK7) )
    | ~ spl13_17 ),
    inference(resolution,[],[f96,f439])).

fof(f439,plain,
    ( ! [X4] :
        ( r1_lattices(sK8,X4,sK9)
        | ~ m1_subset_1(X4,u1_struct_0(sK8))
        | ~ r2_hidden(X4,sK7) )
    | ~ spl13_17 ),
    inference(resolution,[],[f89,f240])).

fof(f240,plain,
    ( sP3(sK9,sK8,sK7)
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f239])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK11(X0,X1,X2),X0)
          & r2_hidden(sK11(X0,X1,X2),X2)
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK11(X0,X1,X2),X0)
        & r2_hidden(sK11(X0,X1,X2),X2)
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f595,plain,
    ( m1_subset_1(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),u1_struct_0(sK8))
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f593])).

fof(f590,plain,
    ( r2_hidden(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK7)
    | ~ spl13_55 ),
    inference(avatar_component_clause,[],[f588])).

fof(f709,plain,
    ( spl13_65
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_56
    | ~ spl13_57 ),
    inference(avatar_split_clause,[],[f704,f598,f593,f136,f131,f126,f121,f706])).

fof(f598,plain,
    ( spl13_57
  <=> sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_57])])).

fof(f704,plain,
    ( k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) = sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_56
    | ~ spl13_57 ),
    inference(forward_demodulation,[],[f679,f600])).

fof(f600,plain,
    ( sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8))
    | ~ spl13_57 ),
    inference(avatar_component_clause,[],[f598])).

fof(f679,plain,
    ( sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) = k7_lattices(sK8,k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)))
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_56 ),
    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f595,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f636,plain,
    ( ~ spl13_58
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_26
    | ~ spl13_35
    | spl13_36 ),
    inference(avatar_split_clause,[],[f635,f407,f402,f327,f183,f173,f168,f136,f121,f610])).

fof(f402,plain,
    ( spl13_35
  <=> m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f407,plain,
    ( spl13_36
  <=> r1_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f635,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_26
    | ~ spl13_35
    | spl13_36 ),
    inference(subsumption_resolution,[],[f634,f138])).

fof(f634,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_26
    | ~ spl13_35
    | spl13_36 ),
    inference(subsumption_resolution,[],[f633,f185])).

fof(f633,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_35
    | spl13_36 ),
    inference(subsumption_resolution,[],[f632,f175])).

fof(f632,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_26
    | ~ spl13_35
    | spl13_36 ),
    inference(subsumption_resolution,[],[f631,f170])).

fof(f631,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_26
    | ~ spl13_35
    | spl13_36 ),
    inference(subsumption_resolution,[],[f630,f123])).

fof(f630,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_26
    | ~ spl13_35
    | spl13_36 ),
    inference(subsumption_resolution,[],[f629,f329])).

fof(f629,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_35
    | spl13_36 ),
    inference(subsumption_resolution,[],[f608,f404])).

fof(f404,plain,
    ( m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8))
    | ~ spl13_35 ),
    inference(avatar_component_clause,[],[f402])).

fof(f608,plain,
    ( ~ r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | ~ m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8))
    | ~ m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | spl13_36 ),
    inference(resolution,[],[f95,f409])).

fof(f409,plain,
    ( ~ r1_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | spl13_36 ),
    inference(avatar_component_clause,[],[f407])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f628,plain,
    ( ~ spl13_59
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_19
    | spl13_20 ),
    inference(avatar_split_clause,[],[f627,f259,f254,f183,f173,f168,f136,f121,f116,f615])).

fof(f254,plain,
    ( spl13_19
  <=> m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f259,plain,
    ( spl13_20
  <=> r1_lattices(sK8,sK11(sK9,sK8,sK7),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f627,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_19
    | spl13_20 ),
    inference(subsumption_resolution,[],[f626,f138])).

fof(f626,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | v2_struct_0(sK8)
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_12
    | ~ spl13_19
    | spl13_20 ),
    inference(subsumption_resolution,[],[f625,f185])).

fof(f625,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_19
    | spl13_20 ),
    inference(subsumption_resolution,[],[f624,f175])).

fof(f624,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_9
    | ~ spl13_19
    | spl13_20 ),
    inference(subsumption_resolution,[],[f623,f170])).

fof(f623,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_19
    | spl13_20 ),
    inference(subsumption_resolution,[],[f622,f123])).

fof(f622,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_3
    | ~ spl13_19
    | spl13_20 ),
    inference(subsumption_resolution,[],[f621,f256])).

fof(f256,plain,
    ( m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8))
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f254])).

fof(f621,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_3
    | spl13_20 ),
    inference(subsumption_resolution,[],[f607,f118])).

fof(f607,plain,
    ( ~ r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ v6_lattices(sK8)
    | v2_struct_0(sK8)
    | spl13_20 ),
    inference(resolution,[],[f95,f261])).

fof(f261,plain,
    ( ~ r1_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | spl13_20 ),
    inference(avatar_component_clause,[],[f259])).

fof(f601,plain,
    ( spl13_57
    | ~ spl13_54 ),
    inference(avatar_split_clause,[],[f584,f577,f598])).

fof(f577,plain,
    ( spl13_54
  <=> sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).

fof(f584,plain,
    ( sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8))
    | ~ spl13_54 ),
    inference(unit_resulting_resolution,[],[f579,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X2,sK12(X0,X1,X2)) = X1
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | k7_lattices(X2,X3) != X1
            | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ( r2_hidden(sK12(X0,X1,X2),X0)
          & k7_lattices(X2,sK12(X0,X1,X2)) = X1
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X2)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & k7_lattices(X2,X4) = X1
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( r2_hidden(sK12(X0,X1,X2),X0)
        & k7_lattices(X2,sK12(X0,X1,X2)) = X1
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | k7_lattices(X2,X3) != X1
            | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & k7_lattices(X2,X4) = X1
            & m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | k7_lattices(X2,X3) != X0
            | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f579,plain,
    ( sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)
    | ~ spl13_54 ),
    inference(avatar_component_clause,[],[f577])).

fof(f596,plain,
    ( spl13_56
    | ~ spl13_54 ),
    inference(avatar_split_clause,[],[f585,f577,f593])).

fof(f585,plain,
    ( m1_subset_1(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),u1_struct_0(sK8))
    | ~ spl13_54 ),
    inference(unit_resulting_resolution,[],[f579,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X2))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f591,plain,
    ( spl13_55
    | ~ spl13_54 ),
    inference(avatar_split_clause,[],[f586,f577,f588])).

fof(f586,plain,
    ( r2_hidden(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK7)
    | ~ spl13_54 ),
    inference(unit_resulting_resolution,[],[f579,f101])).

% (14261)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f582,plain,
    ( spl13_54
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f581,f397,f136,f131,f126,f121,f577])).

fof(f397,plain,
    ( spl13_34
  <=> r2_hidden(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),a_2_0_lattice3(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f581,plain,
    ( sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_34 ),
    inference(subsumption_resolution,[],[f570,f285])).

fof(f570,plain,
    ( sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)
    | ~ sP6(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK7)
    | ~ spl13_34 ),
    inference(resolution,[],[f399,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,a_2_0_lattice3(X2,X0))
      | sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f399,plain,
    ( r2_hidden(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),a_2_0_lattice3(sK7,sK8))
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f397])).

fof(f532,plain,
    ( spl13_48
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7 ),
    inference(avatar_split_clause,[],[f502,f136,f131,f126,f121,f116,f529])).

fof(f502,plain,
    ( sK9 = k7_lattices(sK8,k7_lattices(sK8,sK9))
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7 ),
    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f118,f78])).

fof(f527,plain,
    ( spl13_47
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_35 ),
    inference(avatar_split_clause,[],[f503,f402,f136,f131,f126,f121,f524])).

fof(f503,plain,
    ( sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))))
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_35 ),
    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f404,f78])).

fof(f522,plain,
    ( spl13_46
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f504,f254,f136,f131,f126,f121,f519])).

fof(f504,plain,
    ( sK11(sK9,sK8,sK7) = k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7)))
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | ~ spl13_19 ),
    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f256,f78])).

fof(f491,plain,
    ( spl13_45
    | ~ spl13_4
    | spl13_7
    | ~ spl13_35 ),
    inference(avatar_split_clause,[],[f472,f402,f136,f121,f488])).

fof(f472,plain,
    ( m1_subset_1(k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),u1_struct_0(sK8))
    | ~ spl13_4
    | spl13_7
    | ~ spl13_35 ),
    inference(unit_resulting_resolution,[],[f138,f123,f404,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f410,plain,
    ( ~ spl13_36
    | spl13_30 ),
    inference(avatar_split_clause,[],[f391,f360,f407])).

fof(f391,plain,
    ( ~ r1_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))
    | spl13_30 ),
    inference(unit_resulting_resolution,[],[f362,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK10(X0,X1,X2))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f405,plain,
    ( spl13_35
    | spl13_30 ),
    inference(avatar_split_clause,[],[f392,f360,f402])).

fof(f392,plain,
    ( m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8))
    | spl13_30 ),
    inference(unit_resulting_resolution,[],[f362,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f400,plain,
    ( spl13_34
    | spl13_30 ),
    inference(avatar_split_clause,[],[f394,f360,f397])).

fof(f394,plain,
    ( r2_hidden(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),a_2_0_lattice3(sK7,sK8))
    | spl13_30 ),
    inference(unit_resulting_resolution,[],[f362,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f363,plain,
    ( ~ spl13_30
    | spl13_2
    | ~ spl13_27 ),
    inference(avatar_split_clause,[],[f358,f338,f110,f360])).

fof(f358,plain,
    ( ~ sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))
    | spl13_2
    | ~ spl13_27 ),
    inference(unit_resulting_resolution,[],[f112,f340,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f112,plain,
    ( ~ r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f357,plain,
    ( spl13_27
    | ~ spl13_4
    | spl13_7
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f356,f327,f136,f121,f338])).

fof(f356,plain,
    ( sP2(sK8,k7_lattices(sK8,sK9))
    | ~ spl13_4
    | spl13_7
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f355,f138])).

fof(f355,plain,
    ( sP2(sK8,k7_lattices(sK8,sK9))
    | v2_struct_0(sK8)
    | ~ spl13_4
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f336,f123])).

fof(f336,plain,
    ( sP2(sK8,k7_lattices(sK8,sK9))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_26 ),
    inference(resolution,[],[f329,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f20,f32,f31])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f330,plain,
    ( spl13_26
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7 ),
    inference(avatar_split_clause,[],[f314,f136,f121,f116,f327])).

fof(f314,plain,
    ( m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8))
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7 ),
    inference(unit_resulting_resolution,[],[f138,f123,f118,f94])).

fof(f325,plain,
    ( spl13_25
    | ~ spl13_4
    | spl13_7
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f315,f254,f136,f121,f322])).

fof(f315,plain,
    ( m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8))
    | ~ spl13_4
    | spl13_7
    | ~ spl13_19 ),
    inference(unit_resulting_resolution,[],[f138,f123,f256,f94])).

fof(f297,plain,
    ( spl13_23
    | ~ spl13_18
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f291,f254,f249,f294])).

fof(f249,plain,
    ( spl13_18
  <=> r2_hidden(sK11(sK9,sK8,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f291,plain,
    ( sP5(sK7,k7_lattices(sK8,sK11(sK9,sK8,sK7)),sK8)
    | ~ spl13_18
    | ~ spl13_19 ),
    inference(unit_resulting_resolution,[],[f251,f256,f104])).

fof(f104,plain,(
    ! [X2,X0,X3] :
      ( sP5(X0,k7_lattices(X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X0,X1,X2)
      | ~ r2_hidden(X3,X0)
      | k7_lattices(X2,X3) != X1
      | ~ m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f251,plain,
    ( r2_hidden(sK11(sK9,sK8,sK7),sK7)
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f249])).

fof(f262,plain,
    ( ~ spl13_20
    | spl13_17 ),
    inference(avatar_split_clause,[],[f243,f239,f259])).

fof(f243,plain,
    ( ~ r1_lattices(sK8,sK11(sK9,sK8,sK7),sK9)
    | spl13_17 ),
    inference(unit_resulting_resolution,[],[f241,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK11(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f241,plain,
    ( ~ sP3(sK9,sK8,sK7)
    | spl13_17 ),
    inference(avatar_component_clause,[],[f239])).

fof(f257,plain,
    ( spl13_19
    | spl13_17 ),
    inference(avatar_split_clause,[],[f244,f239,f254])).

fof(f244,plain,
    ( m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8))
    | spl13_17 ),
    inference(unit_resulting_resolution,[],[f241,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f252,plain,
    ( spl13_18
    | spl13_17 ),
    inference(avatar_split_clause,[],[f246,f239,f249])).

fof(f246,plain,
    ( r2_hidden(sK11(sK9,sK8,sK7),sK7)
    | spl13_17 ),
    inference(unit_resulting_resolution,[],[f241,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f242,plain,
    ( ~ spl13_17
    | spl13_1
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f237,f230,f106,f239])).

fof(f237,plain,
    ( ~ sP3(sK9,sK8,sK7)
    | spl13_1
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f108,f232,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f108,plain,
    ( ~ r4_lattice3(sK8,sK9,sK7)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f236,plain,
    ( spl13_16
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7 ),
    inference(avatar_split_clause,[],[f235,f136,f121,f116,f230])).

fof(f235,plain,
    ( sP4(sK8,sK9)
    | ~ spl13_3
    | ~ spl13_4
    | spl13_7 ),
    inference(subsumption_resolution,[],[f234,f138])).

fof(f234,plain,
    ( sP4(sK8,sK9)
    | v2_struct_0(sK8)
    | ~ spl13_3
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f226,f123])).

fof(f226,plain,
    ( sP4(sK8,sK9)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ spl13_3 ),
    inference(resolution,[],[f93,f118])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f35,f34])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f202,plain,
    ( spl13_9
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f166,f149,f168])).

fof(f149,plain,
    ( spl13_8
  <=> sP0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f166,plain,
    ( v9_lattices(sK8)
    | ~ spl13_8 ),
    inference(resolution,[],[f151,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f151,plain,
    ( sP0(sK8)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f201,plain,
    ( spl13_10
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f165,f149,f173])).

fof(f165,plain,
    ( v8_lattices(sK8)
    | ~ spl13_8 ),
    inference(resolution,[],[f151,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f199,plain,
    ( spl13_12
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f163,f149,f183])).

fof(f163,plain,
    ( v6_lattices(sK8)
    | ~ spl13_8 ),
    inference(resolution,[],[f151,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f152,plain,
    ( spl13_8
    | ~ spl13_4
    | ~ spl13_6
    | spl13_7 ),
    inference(avatar_split_clause,[],[f140,f136,f131,f121,f149])).

fof(f140,plain,
    ( sP0(sK8)
    | ~ spl13_4
    | ~ spl13_6
    | spl13_7 ),
    inference(unit_resulting_resolution,[],[f123,f138,f133,f77])).

fof(f77,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f14,f29])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f139,plain,(
    ~ spl13_7 ),
    inference(avatar_split_clause,[],[f63,f136])).

fof(f63,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
      | ~ r4_lattice3(sK8,sK9,sK7) )
    & ( r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
      | r4_lattice3(sK8,sK9,sK7) )
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l3_lattices(sK8)
    & v17_lattices(sK8)
    & v10_lattices(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r4_lattice3(X1,X2,X0) )
            & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | r4_lattice3(X1,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8))
            | ~ r4_lattice3(sK8,X2,sK7) )
          & ( r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8))
            | r4_lattice3(sK8,X2,sK7) )
          & m1_subset_1(X2,u1_struct_0(sK8)) )
      & l3_lattices(sK8)
      & v17_lattices(sK8)
      & v10_lattices(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ( ~ r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8))
          | ~ r4_lattice3(sK8,X2,sK7) )
        & ( r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8))
          | r4_lattice3(sK8,X2,sK7) )
        & m1_subset_1(X2,u1_struct_0(sK8)) )
   => ( ( ~ r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
        | ~ r4_lattice3(sK8,sK9,sK7) )
      & ( r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
        | r4_lattice3(sK8,sK9,sK7) )
      & m1_subset_1(sK9,u1_struct_0(sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v17_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r4_lattice3(X1,X2,X0)
            <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattice3)).

fof(f134,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f64,f131])).

fof(f64,plain,(
    v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,(
    spl13_5 ),
    inference(avatar_split_clause,[],[f65,f126])).

fof(f65,plain,(
    v17_lattices(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f66,f121])).

fof(f66,plain,(
    l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f67,f116])).

fof(f67,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f44])).

fof(f114,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f68,f110,f106])).

fof(f68,plain,
    ( r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
    | r4_lattice3(sK8,sK9,sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f69,f110,f106])).

fof(f69,plain,
    ( ~ r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))
    | ~ r4_lattice3(sK8,sK9,sK7) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (14251)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (14256)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (14262)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (14254)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (14264)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (14267)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (14252)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (14253)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (14250)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (14268)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (14265)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (14249)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (14268)Refutation not found, incomplete strategy% (14268)------------------------------
% 0.21/0.50  % (14268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14268)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14268)Memory used [KB]: 10618
% 0.21/0.50  % (14268)Time elapsed: 0.098 s
% 0.21/0.50  % (14268)------------------------------
% 0.21/0.50  % (14268)------------------------------
% 0.21/0.50  % (14264)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1007,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f113,f114,f119,f124,f129,f134,f139,f152,f199,f201,f202,f236,f242,f252,f257,f262,f297,f325,f330,f357,f363,f400,f405,f410,f491,f522,f527,f532,f582,f591,f596,f601,f628,f636,f709,f715,f730,f790,f815,f818,f831,f888,f1000,f1006])).
% 0.21/0.50  fof(f1006,plain,(
% 0.21/0.50    ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_25 | ~spl13_26 | ~spl13_46 | ~spl13_48 | spl13_59 | ~spl13_89),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1005])).
% 0.21/0.50  fof(f1005,plain,(
% 0.21/0.50    $false | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_25 | ~spl13_26 | ~spl13_46 | ~spl13_48 | spl13_59 | ~spl13_89)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1004,f617])).
% 0.21/0.50  fof(f617,plain,(
% 0.21/0.50    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | spl13_59),
% 0.21/0.50    inference(avatar_component_clause,[],[f615])).
% 0.21/0.50  fof(f615,plain,(
% 0.21/0.50    spl13_59 <=> r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_59])])).
% 0.21/0.50  fof(f1004,plain,(
% 0.21/0.50    r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_25 | ~spl13_26 | ~spl13_46 | ~spl13_48 | ~spl13_89)),
% 0.21/0.50    inference(forward_demodulation,[],[f1003,f521])).
% 0.21/0.50  fof(f521,plain,(
% 0.21/0.50    sK11(sK9,sK8,sK7) = k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~spl13_46),
% 0.21/0.50    inference(avatar_component_clause,[],[f519])).
% 0.21/0.50  fof(f519,plain,(
% 0.21/0.50    spl13_46 <=> sK11(sK9,sK8,sK7) = k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).
% 0.21/0.50  fof(f1003,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7))),sK9) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_25 | ~spl13_26 | ~spl13_48 | ~spl13_89)),
% 0.21/0.50    inference(forward_demodulation,[],[f1001,f531])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    sK9 = k7_lattices(sK8,k7_lattices(sK8,sK9)) | ~spl13_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f529])).
% 0.21/0.50  fof(f529,plain,(
% 0.21/0.50    spl13_48 <=> sK9 = k7_lattices(sK8,k7_lattices(sK8,sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).
% 0.21/0.50  fof(f1001,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7))),k7_lattices(sK8,k7_lattices(sK8,sK9))) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_25 | ~spl13_26 | ~spl13_89)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f329,f324,f991,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) | ~r3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).
% 0.21/0.50  fof(f991,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~spl13_89),
% 0.21/0.50    inference(avatar_component_clause,[],[f989])).
% 0.21/0.50  fof(f989,plain,(
% 0.21/0.50    spl13_89 <=> r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_89])])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8)) | ~spl13_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f322])).
% 0.21/0.50  % (14248)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    spl13_25 <=> m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8)) | ~spl13_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f327])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    spl13_26 <=> m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    l3_lattices(sK8) | ~spl13_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl13_4 <=> l3_lattices(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    v17_lattices(sK8) | ~spl13_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  % (14249)Refutation not found, incomplete strategy% (14249)------------------------------
% 0.21/0.50  % (14249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl13_5 <=> v17_lattices(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 0.21/0.50  % (14249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14249)Memory used [KB]: 10618
% 0.21/0.50  % (14249)Time elapsed: 0.104 s
% 0.21/0.50  % (14249)------------------------------
% 0.21/0.50  % (14249)------------------------------
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    v10_lattices(sK8) | ~spl13_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl13_6 <=> v10_lattices(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v2_struct_0(sK8) | spl13_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl13_7 <=> v2_struct_0(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 0.21/0.50  fof(f1000,plain,(
% 0.21/0.50    spl13_89 | ~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_25 | ~spl13_26 | ~spl13_78),
% 0.21/0.50    inference(avatar_split_clause,[],[f999,f885,f327,f322,f183,f173,f168,f136,f121,f989])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl13_9 <=> v9_lattices(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl13_10 <=> v8_lattices(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    spl13_12 <=> v6_lattices(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 0.21/0.50  fof(f885,plain,(
% 0.21/0.50    spl13_78 <=> r1_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).
% 0.21/0.50  fof(f999,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | (~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_25 | ~spl13_26 | ~spl13_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f998,f138])).
% 0.21/0.50  fof(f998,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_25 | ~spl13_26 | ~spl13_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f997,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    v6_lattices(sK8) | ~spl13_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f183])).
% 0.21/0.50  fof(f997,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_25 | ~spl13_26 | ~spl13_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f996,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    v8_lattices(sK8) | ~spl13_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f173])).
% 0.21/0.50  fof(f996,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_9 | ~spl13_25 | ~spl13_26 | ~spl13_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f995,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    v9_lattices(sK8) | ~spl13_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f995,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_25 | ~spl13_26 | ~spl13_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f994,f123])).
% 0.21/0.50  fof(f994,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_25 | ~spl13_26 | ~spl13_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f993,f329])).
% 0.21/0.50  fof(f993,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_25 | ~spl13_78)),
% 0.21/0.50    inference(subsumption_resolution,[],[f987,f324])).
% 0.21/0.50  fof(f987,plain,(
% 0.21/0.50    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8)) | ~m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | ~spl13_78),
% 0.21/0.50    inference(resolution,[],[f887,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.50  fof(f887,plain,(
% 0.21/0.50    r1_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | ~spl13_78),
% 0.21/0.50    inference(avatar_component_clause,[],[f885])).
% 0.21/0.50  fof(f888,plain,(
% 0.21/0.50    spl13_78 | ~spl13_24 | ~spl13_25 | ~spl13_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f874,f360,f322,f308,f885])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    spl13_24 <=> r2_hidden(k7_lattices(sK8,sK11(sK9,sK8,sK7)),a_2_0_lattice3(sK7,sK8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    spl13_30 <=> sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).
% 0.21/0.50  fof(f874,plain,(
% 0.21/0.50    r1_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,sK11(sK9,sK8,sK7))) | (~spl13_24 | ~spl13_25 | ~spl13_30)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f361,f324,f309,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~r1_lattices(X1,X0,sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP1(X1,X0,X2)))),
% 0.21/0.50    inference(nnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    r2_hidden(k7_lattices(sK8,sK11(sK9,sK8,sK7)),a_2_0_lattice3(sK7,sK8)) | ~spl13_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f308])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) | ~spl13_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f360])).
% 0.21/0.50  fof(f831,plain,(
% 0.21/0.50    ~spl13_2 | ~spl13_27 | spl13_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f393,f360,f338,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl13_2 <=> r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    spl13_27 <=> sP2(sK8,k7_lattices(sK8,sK9))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).
% 0.21/0.50  fof(f393,plain,(
% 0.21/0.50    ~r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | (~spl13_27 | spl13_30)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f340,f362,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP2(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP2(X0,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP1(X1,X0,X2)) | ~sP2(X0,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    ~sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) | spl13_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f360])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    sP2(sK8,k7_lattices(sK8,sK9)) | ~spl13_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f338])).
% 0.21/0.50  fof(f818,plain,(
% 0.21/0.50    ~spl13_23 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | spl13_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f312,f308,f136,f131,f126,f121,f294])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    spl13_23 <=> sP5(sK7,k7_lattices(sK8,sK11(sK9,sK8,sK7)),sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).
% 0.21/0.50  % (14258)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    ~sP5(sK7,k7_lattices(sK8,sK11(sK9,sK8,sK7)),sK8) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | spl13_24)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f285,f310,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X1,a_2_0_lattice3(X2,X0)) | ~sP5(X2,X1,X0) | ~sP6(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X1,a_2_0_lattice3(X2,X0)) | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | ~r2_hidden(X1,a_2_0_lattice3(X2,X0)))) | ~sP6(X0,X1,X2))),
% 0.21/0.50    inference(rectify,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ! [X2,X0,X1] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~sP6(X2,X0,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X2,X0,X1] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> sP5(X1,X0,X2)) | ~sP6(X2,X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    ~r2_hidden(k7_lattices(sK8,sK11(sK9,sK8,sK7)),a_2_0_lattice3(sK7,sK8)) | spl13_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f308])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP6(sK8,X0,X1)) ) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (sP6(X2,X0,X1) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 0.21/0.51    inference(definition_folding,[],[f28,f38,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | (~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((l3_lattices(X2) & v17_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) => (r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).
% 0.21/0.51  fof(f815,plain,(
% 0.21/0.51    spl13_17 | ~spl13_1 | ~spl13_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f299,f230,f106,f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    spl13_17 <=> sP3(sK9,sK8,sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl13_1 <=> r4_lattice3(sK8,sK9,sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    spl13_16 <=> sP4(sK8,sK9)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 0.21/0.51  % (14260)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (14255)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    sP3(sK9,sK8,sK7) | (~spl13_1 | ~spl13_16)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f232,f107,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP4(X0,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP3(X1,X0,X2)) | ~sP4(X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    r4_lattice3(sK8,sK9,sK7) | ~spl13_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    sP4(sK8,sK9) | ~spl13_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f230])).
% 0.21/0.51  fof(f790,plain,(
% 0.21/0.51    ~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_45 | ~spl13_47 | spl13_58 | ~spl13_67),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f789])).
% 0.21/0.51  fof(f789,plain,(
% 0.21/0.51    $false | (~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_45 | ~spl13_47 | spl13_58 | ~spl13_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f788,f612])).
% 0.21/0.51  fof(f612,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | spl13_58),
% 0.21/0.51    inference(avatar_component_clause,[],[f610])).
% 0.21/0.51  fof(f610,plain,(
% 0.21/0.51    spl13_58 <=> r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).
% 0.21/0.51  fof(f788,plain,(
% 0.21/0.51    r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | (~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_45 | ~spl13_47 | ~spl13_67)),
% 0.21/0.51    inference(forward_demodulation,[],[f777,f526])).
% 0.21/0.51  fof(f526,plain,(
% 0.21/0.51    sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))) | ~spl13_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f524])).
% 0.21/0.51  fof(f524,plain,(
% 0.21/0.51    spl13_47 <=> sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_47])])).
% 0.21/0.51  fof(f777,plain,(
% 0.21/0.51    r3_lattices(sK8,k7_lattices(sK8,sK9),k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))))) | (~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_45 | ~spl13_67)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f490,f729,f118,f79])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    m1_subset_1(sK9,u1_struct_0(sK8)) | ~spl13_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl13_3 <=> m1_subset_1(sK9,u1_struct_0(sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.21/0.51  fof(f729,plain,(
% 0.21/0.51    r3_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),sK9) | ~spl13_67),
% 0.21/0.51    inference(avatar_component_clause,[],[f727])).
% 0.21/0.51  fof(f727,plain,(
% 0.21/0.51    spl13_67 <=> r3_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),sK9)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_67])])).
% 0.21/0.51  fof(f490,plain,(
% 0.21/0.51    m1_subset_1(k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),u1_struct_0(sK8)) | ~spl13_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f488])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    spl13_45 <=> m1_subset_1(k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),u1_struct_0(sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).
% 0.21/0.51  fof(f730,plain,(
% 0.21/0.51    spl13_67 | ~spl13_65 | ~spl13_66),
% 0.21/0.51    inference(avatar_split_clause,[],[f722,f712,f706,f727])).
% 0.21/0.51  fof(f706,plain,(
% 0.21/0.51    spl13_65 <=> k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) = sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).
% 0.21/0.51  fof(f712,plain,(
% 0.21/0.51    spl13_66 <=> r3_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK9)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).
% 0.21/0.51  fof(f722,plain,(
% 0.21/0.51    r3_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),sK9) | (~spl13_65 | ~spl13_66)),
% 0.21/0.51    inference(backward_demodulation,[],[f714,f708])).
% 0.21/0.51  fof(f708,plain,(
% 0.21/0.51    k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) = sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) | ~spl13_65),
% 0.21/0.51    inference(avatar_component_clause,[],[f706])).
% 0.21/0.51  fof(f714,plain,(
% 0.21/0.51    r3_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK9) | ~spl13_66),
% 0.21/0.51    inference(avatar_component_clause,[],[f712])).
% 0.21/0.51  fof(f715,plain,(
% 0.21/0.51    spl13_66 | ~spl13_3 | ~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_17 | ~spl13_55 | ~spl13_56),
% 0.21/0.51    inference(avatar_split_clause,[],[f677,f593,f588,f239,f183,f173,f168,f136,f121,f116,f712])).
% 0.21/0.51  fof(f588,plain,(
% 0.21/0.51    spl13_55 <=> r2_hidden(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).
% 0.21/0.51  fof(f593,plain,(
% 0.21/0.51    spl13_56 <=> m1_subset_1(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),u1_struct_0(sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).
% 0.21/0.51  fof(f677,plain,(
% 0.21/0.51    r3_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK9) | (~spl13_3 | ~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_17 | ~spl13_55 | ~spl13_56)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f590,f595,f674])).
% 0.21/0.51  fof(f674,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~r2_hidden(X0,sK7)) ) | (~spl13_3 | ~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f673,f138])).
% 0.21/0.51  fof(f673,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(X0,u1_struct_0(sK8)) | v2_struct_0(sK8) | ~r2_hidden(X0,sK7)) ) | (~spl13_3 | ~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f672,f185])).
% 0.21/0.51  fof(f672,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~v6_lattices(sK8) | v2_struct_0(sK8) | ~r2_hidden(X0,sK7)) ) | (~spl13_3 | ~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f671,f175])).
% 0.21/0.51  fof(f671,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | ~r2_hidden(X0,sK7)) ) | (~spl13_3 | ~spl13_4 | ~spl13_9 | ~spl13_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f670,f170])).
% 0.21/0.51  fof(f670,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | ~r2_hidden(X0,sK7)) ) | (~spl13_3 | ~spl13_4 | ~spl13_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f669,f123])).
% 0.21/0.51  fof(f669,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | ~r2_hidden(X0,sK7)) ) | (~spl13_3 | ~spl13_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f668,f118])).
% 0.21/0.51  fof(f668,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | ~r2_hidden(X0,sK7)) ) | ~spl13_17),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f665])).
% 0.21/0.51  fof(f665,plain,(
% 0.21/0.51    ( ! [X0] : (r3_lattices(sK8,X0,sK9) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~r2_hidden(X0,sK7)) ) | ~spl13_17),
% 0.21/0.51    inference(resolution,[],[f96,f439])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    ( ! [X4] : (r1_lattices(sK8,X4,sK9) | ~m1_subset_1(X4,u1_struct_0(sK8)) | ~r2_hidden(X4,sK7)) ) | ~spl13_17),
% 0.21/0.51    inference(resolution,[],[f89,f240])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    sP3(sK9,sK8,sK7) | ~spl13_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f239])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,sK11(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK11(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X1,X0,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.51  fof(f595,plain,(
% 0.21/0.51    m1_subset_1(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),u1_struct_0(sK8)) | ~spl13_56),
% 0.21/0.51    inference(avatar_component_clause,[],[f593])).
% 0.21/0.51  fof(f590,plain,(
% 0.21/0.51    r2_hidden(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK7) | ~spl13_55),
% 0.21/0.51    inference(avatar_component_clause,[],[f588])).
% 0.21/0.51  fof(f709,plain,(
% 0.21/0.51    spl13_65 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_56 | ~spl13_57),
% 0.21/0.51    inference(avatar_split_clause,[],[f704,f598,f593,f136,f131,f126,f121,f706])).
% 0.21/0.51  fof(f598,plain,(
% 0.21/0.51    spl13_57 <=> sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_57])])).
% 0.21/0.51  fof(f704,plain,(
% 0.21/0.51    k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) = sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_56 | ~spl13_57)),
% 0.21/0.51    inference(forward_demodulation,[],[f679,f600])).
% 0.21/0.51  fof(f600,plain,(
% 0.21/0.51    sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)) | ~spl13_57),
% 0.21/0.51    inference(avatar_component_clause,[],[f598])).
% 0.21/0.51  fof(f679,plain,(
% 0.21/0.51    sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) = k7_lattices(sK8,k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8))) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_56)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f595,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).
% 0.21/0.51  fof(f636,plain,(
% 0.21/0.51    ~spl13_58 | ~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_26 | ~spl13_35 | spl13_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f635,f407,f402,f327,f183,f173,f168,f136,f121,f610])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    spl13_35 <=> m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    spl13_36 <=> r1_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).
% 0.21/0.51  fof(f635,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | (~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_26 | ~spl13_35 | spl13_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f634,f138])).
% 0.21/0.51  fof(f634,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_26 | ~spl13_35 | spl13_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f633,f185])).
% 0.21/0.51  fof(f633,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_26 | ~spl13_35 | spl13_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f632,f175])).
% 0.21/0.51  fof(f632,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_9 | ~spl13_26 | ~spl13_35 | spl13_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f631,f170])).
% 0.21/0.51  fof(f631,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_26 | ~spl13_35 | spl13_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f630,f123])).
% 0.21/0.51  fof(f630,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_26 | ~spl13_35 | spl13_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f629,f329])).
% 0.21/0.51  fof(f629,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | ~m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_35 | spl13_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f608,f404])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8)) | ~spl13_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f402])).
% 0.21/0.51  fof(f608,plain,(
% 0.21/0.51    ~r3_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | ~m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8)) | ~m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | spl13_36),
% 0.21/0.51    inference(resolution,[],[f95,f409])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ~r1_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | spl13_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f407])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f56])).
% 0.21/0.51  fof(f628,plain,(
% 0.21/0.51    ~spl13_59 | ~spl13_3 | ~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_19 | spl13_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f627,f259,f254,f183,f173,f168,f136,f121,f116,f615])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    spl13_19 <=> m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    spl13_20 <=> r1_lattices(sK8,sK11(sK9,sK8,sK7),sK9)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).
% 0.21/0.51  fof(f627,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | (~spl13_3 | ~spl13_4 | spl13_7 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_19 | spl13_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f626,f138])).
% 0.21/0.51  fof(f626,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | v2_struct_0(sK8) | (~spl13_3 | ~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_12 | ~spl13_19 | spl13_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f625,f185])).
% 0.21/0.51  fof(f625,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_3 | ~spl13_4 | ~spl13_9 | ~spl13_10 | ~spl13_19 | spl13_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f624,f175])).
% 0.21/0.51  fof(f624,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_3 | ~spl13_4 | ~spl13_9 | ~spl13_19 | spl13_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f623,f170])).
% 0.21/0.51  fof(f623,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_3 | ~spl13_4 | ~spl13_19 | spl13_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f622,f123])).
% 0.21/0.51  fof(f622,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_3 | ~spl13_19 | spl13_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f621,f256])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8)) | ~spl13_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f254])).
% 0.21/0.51  fof(f621,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | ~m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | (~spl13_3 | spl13_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f607,f118])).
% 0.21/0.51  fof(f607,plain,(
% 0.21/0.51    ~r3_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v9_lattices(sK8) | ~v8_lattices(sK8) | ~v6_lattices(sK8) | v2_struct_0(sK8) | spl13_20),
% 0.21/0.51    inference(resolution,[],[f95,f261])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ~r1_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | spl13_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f259])).
% 0.21/0.51  fof(f601,plain,(
% 0.21/0.51    spl13_57 | ~spl13_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f584,f577,f598])).
% 0.21/0.51  fof(f577,plain,(
% 0.21/0.51    spl13_54 <=> sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).
% 0.21/0.51  fof(f584,plain,(
% 0.21/0.51    sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8)) | ~spl13_54),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f579,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_lattices(X2,sK12(X0,X1,X2)) = X1 | ~sP5(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | k7_lattices(X2,X3) != X1 | ~m1_subset_1(X3,u1_struct_0(X2)))) & ((r2_hidden(sK12(X0,X1,X2),X0) & k7_lattices(X2,sK12(X0,X1,X2)) = X1 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X2))) | ~sP5(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f60,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & k7_lattices(X2,X4) = X1 & m1_subset_1(X4,u1_struct_0(X2))) => (r2_hidden(sK12(X0,X1,X2),X0) & k7_lattices(X2,sK12(X0,X1,X2)) = X1 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | k7_lattices(X2,X3) != X1 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X4] : (r2_hidden(X4,X0) & k7_lattices(X2,X4) = X1 & m1_subset_1(X4,u1_struct_0(X2))) | ~sP5(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2))) | ~sP5(X1,X0,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f37])).
% 0.21/0.51  fof(f579,plain,(
% 0.21/0.51    sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) | ~spl13_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f577])).
% 0.21/0.51  fof(f596,plain,(
% 0.21/0.51    spl13_56 | ~spl13_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f585,f577,f593])).
% 0.21/0.51  fof(f585,plain,(
% 0.21/0.51    m1_subset_1(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),u1_struct_0(sK8)) | ~spl13_54),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f579,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X2)) | ~sP5(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f62])).
% 0.21/0.51  fof(f591,plain,(
% 0.21/0.51    spl13_55 | ~spl13_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f586,f577,f588])).
% 0.21/0.51  fof(f586,plain,(
% 0.21/0.51    r2_hidden(sK12(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8),sK7) | ~spl13_54),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f579,f101])).
% 0.21/0.51  % (14261)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK12(X0,X1,X2),X0) | ~sP5(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f62])).
% 0.21/0.51  fof(f582,plain,(
% 0.21/0.51    spl13_54 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_34),
% 0.21/0.51    inference(avatar_split_clause,[],[f581,f397,f136,f131,f126,f121,f577])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    spl13_34 <=> r2_hidden(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),a_2_0_lattice3(sK7,sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 0.21/0.51  fof(f581,plain,(
% 0.21/0.51    sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f570,f285])).
% 0.21/0.51  fof(f570,plain,(
% 0.21/0.51    sP5(sK7,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK8) | ~sP6(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),sK7) | ~spl13_34),
% 0.21/0.51    inference(resolution,[],[f399,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,a_2_0_lattice3(X2,X0)) | sP5(X2,X1,X0) | ~sP6(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f58])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    r2_hidden(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),a_2_0_lattice3(sK7,sK8)) | ~spl13_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f397])).
% 0.21/0.51  fof(f532,plain,(
% 0.21/0.51    spl13_48 | ~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f502,f136,f131,f126,f121,f116,f529])).
% 0.21/0.51  fof(f502,plain,(
% 0.21/0.51    sK9 = k7_lattices(sK8,k7_lattices(sK8,sK9)) | (~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f118,f78])).
% 0.21/0.51  fof(f527,plain,(
% 0.21/0.51    spl13_47 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_35),
% 0.21/0.51    inference(avatar_split_clause,[],[f503,f402,f136,f131,f126,f121,f524])).
% 0.21/0.51  fof(f503,plain,(
% 0.21/0.51    sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) = k7_lattices(sK8,k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)))) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_35)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f404,f78])).
% 0.21/0.51  fof(f522,plain,(
% 0.21/0.51    spl13_46 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f504,f254,f136,f131,f126,f121,f519])).
% 0.21/0.51  fof(f504,plain,(
% 0.21/0.51    sK11(sK9,sK8,sK7) = k7_lattices(sK8,k7_lattices(sK8,sK11(sK9,sK8,sK7))) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | ~spl13_19)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f133,f128,f123,f256,f78])).
% 0.21/0.51  fof(f491,plain,(
% 0.21/0.51    spl13_45 | ~spl13_4 | spl13_7 | ~spl13_35),
% 0.21/0.51    inference(avatar_split_clause,[],[f472,f402,f136,f121,f488])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    m1_subset_1(k7_lattices(sK8,sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))),u1_struct_0(sK8)) | (~spl13_4 | spl13_7 | ~spl13_35)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f123,f404,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    ~spl13_36 | spl13_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f391,f360,f407])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    ~r1_lattices(sK8,k7_lattices(sK8,sK9),sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8))) | spl13_30),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f362,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK10(X0,X1,X2)) | sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    spl13_35 | spl13_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f392,f360,f402])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    m1_subset_1(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),u1_struct_0(sK8)) | spl13_30),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f362,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) | sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    spl13_34 | spl13_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f394,f360,f397])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    r2_hidden(sK10(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)),a_2_0_lattice3(sK7,sK8)) | spl13_30),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f362,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X2) | sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f363,plain,(
% 0.21/0.51    ~spl13_30 | spl13_2 | ~spl13_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f358,f338,f110,f360])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    ~sP1(k7_lattices(sK8,sK9),sK8,a_2_0_lattice3(sK7,sK8)) | (spl13_2 | ~spl13_27)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f112,f340,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP1(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP2(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | spl13_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    spl13_27 | ~spl13_4 | spl13_7 | ~spl13_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f356,f327,f136,f121,f338])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    sP2(sK8,k7_lattices(sK8,sK9)) | (~spl13_4 | spl13_7 | ~spl13_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f355,f138])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    sP2(sK8,k7_lattices(sK8,sK9)) | v2_struct_0(sK8) | (~spl13_4 | ~spl13_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f336,f123])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    sP2(sK8,k7_lattices(sK8,sK9)) | ~l3_lattices(sK8) | v2_struct_0(sK8) | ~spl13_26),
% 0.21/0.51    inference(resolution,[],[f329,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (sP2(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f20,f32,f31])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.21/0.51  fof(f330,plain,(
% 0.21/0.51    spl13_26 | ~spl13_3 | ~spl13_4 | spl13_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f314,f136,f121,f116,f327])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    m1_subset_1(k7_lattices(sK8,sK9),u1_struct_0(sK8)) | (~spl13_3 | ~spl13_4 | spl13_7)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f123,f118,f94])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    spl13_25 | ~spl13_4 | spl13_7 | ~spl13_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f315,f254,f136,f121,f322])).
% 0.21/0.51  fof(f315,plain,(
% 0.21/0.51    m1_subset_1(k7_lattices(sK8,sK11(sK9,sK8,sK7)),u1_struct_0(sK8)) | (~spl13_4 | spl13_7 | ~spl13_19)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f138,f123,f256,f94])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    spl13_23 | ~spl13_18 | ~spl13_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f291,f254,f249,f294])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    spl13_18 <=> r2_hidden(sK11(sK9,sK8,sK7),sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    sP5(sK7,k7_lattices(sK8,sK11(sK9,sK8,sK7)),sK8) | (~spl13_18 | ~spl13_19)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f251,f256,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (sP5(X0,k7_lattices(X2,X3),X2) | ~r2_hidden(X3,X0) | ~m1_subset_1(X3,u1_struct_0(X2))) )),
% 0.21/0.51    inference(equality_resolution,[],[f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (sP5(X0,X1,X2) | ~r2_hidden(X3,X0) | k7_lattices(X2,X3) != X1 | ~m1_subset_1(X3,u1_struct_0(X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f62])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    r2_hidden(sK11(sK9,sK8,sK7),sK7) | ~spl13_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f249])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    ~spl13_20 | spl13_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f243,f239,f259])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ~r1_lattices(sK8,sK11(sK9,sK8,sK7),sK9) | spl13_17),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f241,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK11(X0,X1,X2),X0) | sP3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ~sP3(sK9,sK8,sK7) | spl13_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f239])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    spl13_19 | spl13_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f244,f239,f254])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    m1_subset_1(sK11(sK9,sK8,sK7),u1_struct_0(sK8)) | spl13_17),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f241,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    spl13_18 | spl13_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f246,f239,f249])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    r2_hidden(sK11(sK9,sK8,sK7),sK7) | spl13_17),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f241,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ~spl13_17 | spl13_1 | ~spl13_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f237,f230,f106,f239])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ~sP3(sK9,sK8,sK7) | (spl13_1 | ~spl13_16)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f108,f232,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP3(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~r4_lattice3(sK8,sK9,sK7) | spl13_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    spl13_16 | ~spl13_3 | ~spl13_4 | spl13_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f235,f136,f121,f116,f230])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    sP4(sK8,sK9) | (~spl13_3 | ~spl13_4 | spl13_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f234,f138])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    sP4(sK8,sK9) | v2_struct_0(sK8) | (~spl13_3 | ~spl13_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f226,f123])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    sP4(sK8,sK9) | ~l3_lattices(sK8) | v2_struct_0(sK8) | ~spl13_3),
% 0.21/0.51    inference(resolution,[],[f93,f118])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP4(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (sP4(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f22,f35,f34])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    spl13_9 | ~spl13_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f166,f149,f168])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl13_8 <=> sP0(sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    v9_lattices(sK8) | ~spl13_8),
% 0.21/0.51    inference(resolution,[],[f151,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    sP0(sK8) | ~spl13_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl13_10 | ~spl13_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f165,f149,f173])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    v8_lattices(sK8) | ~spl13_8),
% 0.21/0.51    inference(resolution,[],[f151,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    spl13_12 | ~spl13_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f149,f183])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    v6_lattices(sK8) | ~spl13_8),
% 0.21/0.51    inference(resolution,[],[f151,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl13_8 | ~spl13_4 | ~spl13_6 | spl13_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f140,f136,f131,f121,f149])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    sP0(sK8) | (~spl13_4 | ~spl13_6 | spl13_7)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f123,f138,f133,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.51    inference(definition_folding,[],[f14,f29])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~spl13_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f63,f136])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~v2_struct_0(sK8)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ((~r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | ~r4_lattice3(sK8,sK9,sK7)) & (r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | r4_lattice3(sK8,sK9,sK7)) & m1_subset_1(sK9,u1_struct_0(sK8))) & l3_lattices(sK8) & v17_lattices(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f41,f43,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0)) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (? [X2] : ((~r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8)) | ~r4_lattice3(sK8,X2,sK7)) & (r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8)) | r4_lattice3(sK8,X2,sK7)) & m1_subset_1(X2,u1_struct_0(sK8))) & l3_lattices(sK8) & v17_lattices(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ? [X2] : ((~r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8)) | ~r4_lattice3(sK8,X2,sK7)) & (r3_lattice3(sK8,k7_lattices(sK8,X2),a_2_0_lattice3(sK7,sK8)) | r4_lattice3(sK8,X2,sK7)) & m1_subset_1(X2,u1_struct_0(sK8))) => ((~r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | ~r4_lattice3(sK8,sK9,sK7)) & (r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | r4_lattice3(sK8,sK9,sK7)) & m1_subset_1(sK9,u1_struct_0(sK8)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0)) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (((~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0)) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,X2,X0))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattice3)).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl13_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f64,f131])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    v10_lattices(sK8)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl13_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f65,f126])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    v17_lattices(sK8)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl13_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f121])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    l3_lattices(sK8)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl13_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f67,f116])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    m1_subset_1(sK9,u1_struct_0(sK8))),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl13_1 | spl13_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f110,f106])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | r4_lattice3(sK8,sK9,sK7)),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~spl13_1 | ~spl13_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f69,f110,f106])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ~r3_lattice3(sK8,k7_lattices(sK8,sK9),a_2_0_lattice3(sK7,sK8)) | ~r4_lattice3(sK8,sK9,sK7)),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14264)------------------------------
% 0.21/0.52  % (14264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14264)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14264)Memory used [KB]: 11385
% 0.21/0.52  % (14264)Time elapsed: 0.100 s
% 0.21/0.52  % (14264)------------------------------
% 0.21/0.52  % (14264)------------------------------
% 0.21/0.52  % (14259)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (14263)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (14247)Success in time 0.162 s
%------------------------------------------------------------------------------
