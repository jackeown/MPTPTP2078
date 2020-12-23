%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:53 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 336 expanded)
%              Number of leaves         :   44 ( 128 expanded)
%              Depth                    :    9
%              Number of atoms          :  570 (1391 expanded)
%              Number of equality atoms :   28 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f138,f139,f145,f157,f180,f206,f220,f240,f371,f713,f715,f853,f978,f979,f991,f2557,f2580,f2619,f2663,f2664,f2799,f3262])).

fof(f3262,plain,(
    ~ spl9_245 ),
    inference(avatar_contradiction_clause,[],[f3261])).

fof(f3261,plain,
    ( $false
    | ~ spl9_245 ),
    inference(resolution,[],[f2798,f230])).

fof(f230,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f78,f207])).

fof(f207,plain,(
    ! [X1] : sK6(X1) = X1 ),
    inference(global_subsumption,[],[f78,f201])).

fof(f201,plain,(
    ! [X1] :
      ( sK6(X1) = X1
      | v1_subset_1(sK6(X1),X1) ) ),
    inference(resolution,[],[f82,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f78,plain,(
    ! [X0] : ~ v1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2798,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl9_245 ),
    inference(avatar_component_clause,[],[f2796])).

fof(f2796,plain,
    ( spl9_245
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_245])])).

fof(f2799,plain,
    ( spl9_245
    | ~ spl9_8
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f2690,f203,f131,f2796])).

fof(f131,plain,
    ( spl9_8
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f203,plain,
    ( spl9_19
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f2690,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl9_8
    | ~ spl9_19 ),
    inference(backward_demodulation,[],[f132,f205])).

fof(f205,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f132,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f2664,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2663,plain,
    ( ~ spl9_59
    | ~ spl9_9
    | ~ spl9_10
    | spl9_97
    | ~ spl9_35
    | ~ spl9_235 ),
    inference(avatar_split_clause,[],[f2660,f2614,f383,f895,f142,f135,f528])).

fof(f528,plain,
    ( spl9_59
  <=> m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f135,plain,
    ( spl9_9
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f142,plain,
    ( spl9_10
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f895,plain,
    ( spl9_97
  <=> r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f383,plain,
    ( spl9_35
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,sK1)
        | ~ r1_orders_2(sK0,X3,X4)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f2614,plain,
    ( spl9_235
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_235])])).

fof(f2660,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_35
    | ~ spl9_235 ),
    inference(resolution,[],[f2616,f384])).

fof(f384,plain,
    ( ! [X4,X3] :
        ( ~ r1_orders_2(sK0,X3,X4)
        | r2_hidden(X4,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f383])).

fof(f2616,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | ~ spl9_235 ),
    inference(avatar_component_clause,[],[f2614])).

fof(f2619,plain,
    ( ~ spl9_59
    | ~ spl9_22
    | spl9_235
    | ~ spl9_12
    | ~ spl9_33
    | ~ spl9_228 ),
    inference(avatar_split_clause,[],[f2618,f2554,f369,f154,f2614,f237,f528])).

fof(f237,plain,
    ( spl9_22
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f154,plain,
    ( spl9_12
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f369,plain,
    ( spl9_33
  <=> ! [X1,X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f2554,plain,
    ( spl9_228
  <=> r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_228])])).

fof(f2618,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | ~ r1_yellow_0(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_12
    | ~ spl9_33
    | ~ spl9_228 ),
    inference(forward_demodulation,[],[f2609,f156])).

fof(f156,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f2609,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | ~ r1_yellow_0(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_33
    | ~ spl9_228 ),
    inference(resolution,[],[f2556,f370])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f369])).

fof(f2556,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | ~ spl9_228 ),
    inference(avatar_component_clause,[],[f2554])).

fof(f2580,plain,(
    ~ spl9_227 ),
    inference(avatar_contradiction_clause,[],[f2576])).

fof(f2576,plain,
    ( $false
    | ~ spl9_227 ),
    inference(resolution,[],[f2568,f198])).

fof(f198,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f89,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2568,plain,
    ( ! [X2] : ~ r1_tarski(X2,sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))
    | ~ spl9_227 ),
    inference(resolution,[],[f2552,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2552,plain,
    ( ! [X4] : r2_hidden(sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X4)
    | ~ spl9_227 ),
    inference(avatar_component_clause,[],[f2551])).

fof(f2551,plain,
    ( spl9_227
  <=> ! [X4] : r2_hidden(sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_227])])).

fof(f2557,plain,
    ( spl9_227
    | spl9_228
    | ~ spl9_91 ),
    inference(avatar_split_clause,[],[f2544,f851,f2554,f2551])).

fof(f851,plain,
    ( spl9_91
  <=> ! [X3] :
        ( r2_hidden(sK5(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X3)
        | r2_lattice3(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f2544,plain,
    ( ! [X4] :
        ( r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
        | r2_hidden(sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X4) )
    | ~ spl9_91 ),
    inference(resolution,[],[f852,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f84,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f852,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X3)
        | r2_lattice3(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )
    | ~ spl9_91 ),
    inference(avatar_component_clause,[],[f851])).

fof(f991,plain,(
    spl9_107 ),
    inference(avatar_contradiction_clause,[],[f990])).

fof(f990,plain,
    ( $false
    | spl9_107 ),
    inference(resolution,[],[f977,f229])).

fof(f229,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f77,f207])).

fof(f977,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl9_107 ),
    inference(avatar_component_clause,[],[f975])).

fof(f975,plain,
    ( spl9_107
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).

fof(f979,plain,
    ( spl9_92
    | ~ spl9_5
    | ~ spl9_97 ),
    inference(avatar_split_clause,[],[f970,f895,f116,f855])).

fof(f855,plain,
    ( spl9_92
  <=> r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f116,plain,
    ( spl9_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f970,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_5
    | ~ spl9_97 ),
    inference(resolution,[],[f897,f222])).

fof(f222,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,u1_struct_0(sK0)) )
    | ~ spl9_5 ),
    inference(resolution,[],[f84,f118])).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f897,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl9_97 ),
    inference(avatar_component_clause,[],[f895])).

fof(f978,plain,
    ( spl9_19
    | ~ spl9_92
    | ~ spl9_107
    | ~ spl9_5
    | ~ spl9_97 ),
    inference(avatar_split_clause,[],[f969,f895,f116,f975,f855,f203])).

fof(f969,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl9_97 ),
    inference(resolution,[],[f897,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f853,plain,
    ( spl9_91
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(avatar_split_clause,[],[f840,f528,f96,f851])).

fof(f96,plain,
    ( spl9_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f840,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X3)
        | r2_lattice3(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )
    | ~ spl9_59 ),
    inference(resolution,[],[f530,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f530,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f528])).

fof(f715,plain,
    ( spl9_19
    | spl9_59
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f711,f116,f528,f203])).

fof(f711,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl9_5 ),
    inference(resolution,[],[f118,f298])).

fof(f298,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | m1_subset_1(sK7(X4,X4,X3),X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f87,f229])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK7(X0,X1,X2),X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f713,plain,
    ( ~ spl9_6
    | spl9_35
    | ~ spl9_1
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f699,f116,f96,f383,f121])).

fof(f121,plain,
    ( spl9_6
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f699,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f118,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f371,plain,
    ( spl9_33
    | ~ spl9_1
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f366,f96,f96,f369])).

fof(f366,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl9_1 ),
    inference(resolution,[],[f93,f158])).

fof(f158,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f79,f98])).

fof(f98,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f240,plain,
    ( spl9_22
    | ~ spl9_1
    | spl9_4
    | ~ spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f235,f101,f106,f111,f96,f237])).

fof(f111,plain,
    ( spl9_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f106,plain,
    ( spl9_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f101,plain,
    ( spl9_2
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f235,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl9_2 ),
    inference(resolution,[],[f76,f103])).

fof(f103,plain,
    ( v1_yellow_0(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f220,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f206,plain,
    ( spl9_8
    | spl9_19
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f200,f116,f203,f131])).

fof(f200,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_5 ),
    inference(resolution,[],[f82,f118])).

fof(f180,plain,
    ( spl9_15
    | spl9_16
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f162,f142,f177,f173])).

fof(f173,plain,
    ( spl9_15
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f177,plain,
    ( spl9_16
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f162,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(resolution,[],[f81,f144])).

fof(f144,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f157,plain,
    ( spl9_12
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f152,f96,f154])).

fof(f152,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl9_1 ),
    inference(resolution,[],[f60,f98])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f145,plain,
    ( spl9_10
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f140,f96,f142])).

fof(f140,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f59,f98])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f139,plain,
    ( spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f49,f135,f131])).

fof(f49,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f138,plain,
    ( ~ spl9_8
    | spl9_9 ),
    inference(avatar_split_clause,[],[f50,f135,f131])).

fof(f50,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f129,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f51,f126])).

fof(f126,plain,
    ( spl9_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f124,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f52,f121])).

fof(f52,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f119,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f53,f116])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,(
    ~ spl9_4 ),
    inference(avatar_split_clause,[],[f54,f111])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f109,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f55,f106])).

fof(f55,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f56,f101])).

fof(f56,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f57,f96])).

fof(f57,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:32:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.53  % (17917)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.20/0.53  % (17901)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  % (17903)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (17905)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.54  % (17923)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.54  % (17927)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.54  % (17909)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.54  % (17904)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.54  % (17906)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.55  % (17915)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.55  % (17900)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.55  % (17929)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.55  % (17908)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.55  % (17919)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.55  % (17907)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.55  % (17928)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.55  % (17922)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.56  % (17925)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.56  % (17921)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.56  % (17911)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.56  % (17920)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.56  % (17913)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.56  % (17910)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.56  % (17916)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.56  % (17902)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.56  % (17912)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.57  % (17914)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.57  % (17924)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.59  % (17926)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.61  % (17918)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 3.13/0.79  % (17916)Refutation found. Thanks to Tanya!
% 3.13/0.79  % SZS status Theorem for theBenchmark
% 3.13/0.79  % SZS output start Proof for theBenchmark
% 3.40/0.81  fof(f3263,plain,(
% 3.40/0.81    $false),
% 3.40/0.81    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f138,f139,f145,f157,f180,f206,f220,f240,f371,f713,f715,f853,f978,f979,f991,f2557,f2580,f2619,f2663,f2664,f2799,f3262])).
% 3.40/0.81  fof(f3262,plain,(
% 3.40/0.81    ~spl9_245),
% 3.40/0.81    inference(avatar_contradiction_clause,[],[f3261])).
% 3.40/0.81  fof(f3261,plain,(
% 3.40/0.81    $false | ~spl9_245),
% 3.40/0.81    inference(resolution,[],[f2798,f230])).
% 3.40/0.81  fof(f230,plain,(
% 3.40/0.81    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 3.40/0.81    inference(backward_demodulation,[],[f78,f207])).
% 3.40/0.81  fof(f207,plain,(
% 3.40/0.81    ( ! [X1] : (sK6(X1) = X1) )),
% 3.40/0.81    inference(global_subsumption,[],[f78,f201])).
% 3.40/0.81  fof(f201,plain,(
% 3.40/0.81    ( ! [X1] : (sK6(X1) = X1 | v1_subset_1(sK6(X1),X1)) )),
% 3.40/0.81    inference(resolution,[],[f82,f77])).
% 3.40/0.81  fof(f77,plain,(
% 3.40/0.81    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(X0))) )),
% 3.40/0.81    inference(cnf_transformation,[],[f5])).
% 3.40/0.81  fof(f5,axiom,(
% 3.40/0.81    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 3.40/0.81  fof(f82,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f41])).
% 3.40/0.81  fof(f41,plain,(
% 3.40/0.81    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.40/0.81    inference(ennf_transformation,[],[f17])).
% 3.40/0.81  fof(f17,axiom,(
% 3.40/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 3.40/0.81  fof(f78,plain,(
% 3.40/0.81    ( ! [X0] : (~v1_subset_1(sK6(X0),X0)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f5])).
% 3.40/0.81  fof(f2798,plain,(
% 3.40/0.81    v1_subset_1(sK1,sK1) | ~spl9_245),
% 3.40/0.81    inference(avatar_component_clause,[],[f2796])).
% 3.40/0.81  fof(f2796,plain,(
% 3.40/0.81    spl9_245 <=> v1_subset_1(sK1,sK1)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_245])])).
% 3.40/0.81  fof(f2799,plain,(
% 3.40/0.81    spl9_245 | ~spl9_8 | ~spl9_19),
% 3.40/0.81    inference(avatar_split_clause,[],[f2690,f203,f131,f2796])).
% 3.40/0.81  fof(f131,plain,(
% 3.40/0.81    spl9_8 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 3.40/0.81  fof(f203,plain,(
% 3.40/0.81    spl9_19 <=> sK1 = u1_struct_0(sK0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 3.40/0.81  fof(f2690,plain,(
% 3.40/0.81    v1_subset_1(sK1,sK1) | (~spl9_8 | ~spl9_19)),
% 3.40/0.81    inference(backward_demodulation,[],[f132,f205])).
% 3.40/0.81  fof(f205,plain,(
% 3.40/0.81    sK1 = u1_struct_0(sK0) | ~spl9_19),
% 3.40/0.81    inference(avatar_component_clause,[],[f203])).
% 3.40/0.81  fof(f132,plain,(
% 3.40/0.81    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl9_8),
% 3.40/0.81    inference(avatar_component_clause,[],[f131])).
% 3.40/0.81  fof(f2664,plain,(
% 3.40/0.81    sK1 != u1_struct_0(sK0) | v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 3.40/0.81    introduced(theory_tautology_sat_conflict,[])).
% 3.40/0.81  fof(f2663,plain,(
% 3.40/0.81    ~spl9_59 | ~spl9_9 | ~spl9_10 | spl9_97 | ~spl9_35 | ~spl9_235),
% 3.40/0.81    inference(avatar_split_clause,[],[f2660,f2614,f383,f895,f142,f135,f528])).
% 3.40/0.81  fof(f528,plain,(
% 3.40/0.81    spl9_59 <=> m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 3.40/0.81  fof(f135,plain,(
% 3.40/0.81    spl9_9 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 3.40/0.81  fof(f142,plain,(
% 3.40/0.81    spl9_10 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 3.40/0.81  fof(f895,plain,(
% 3.40/0.81    spl9_97 <=> r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).
% 3.40/0.81  fof(f383,plain,(
% 3.40/0.81    spl9_35 <=> ! [X3,X4] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X4,sK1) | ~r1_orders_2(sK0,X3,X4) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 3.40/0.81  fof(f2614,plain,(
% 3.40/0.81    spl9_235 <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_235])])).
% 3.40/0.81  fof(f2660,plain,(
% 3.40/0.81    r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl9_35 | ~spl9_235)),
% 3.40/0.81    inference(resolution,[],[f2616,f384])).
% 3.40/0.81  fof(f384,plain,(
% 3.40/0.81    ( ! [X4,X3] : (~r1_orders_2(sK0,X3,X4) | r2_hidden(X4,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | ~spl9_35),
% 3.40/0.81    inference(avatar_component_clause,[],[f383])).
% 3.40/0.81  fof(f2616,plain,(
% 3.40/0.81    r1_orders_2(sK0,k3_yellow_0(sK0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) | ~spl9_235),
% 3.40/0.81    inference(avatar_component_clause,[],[f2614])).
% 3.40/0.81  fof(f2619,plain,(
% 3.40/0.81    ~spl9_59 | ~spl9_22 | spl9_235 | ~spl9_12 | ~spl9_33 | ~spl9_228),
% 3.40/0.81    inference(avatar_split_clause,[],[f2618,f2554,f369,f154,f2614,f237,f528])).
% 3.40/0.81  fof(f237,plain,(
% 3.40/0.81    spl9_22 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 3.40/0.81  fof(f154,plain,(
% 3.40/0.81    spl9_12 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 3.40/0.81  fof(f369,plain,(
% 3.40/0.81    spl9_33 <=> ! [X1,X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) | ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 3.40/0.81  fof(f2554,plain,(
% 3.40/0.81    spl9_228 <=> r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_228])])).
% 3.40/0.81  fof(f2618,plain,(
% 3.40/0.81    r1_orders_2(sK0,k3_yellow_0(sK0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl9_12 | ~spl9_33 | ~spl9_228)),
% 3.40/0.81    inference(forward_demodulation,[],[f2609,f156])).
% 3.40/0.81  fof(f156,plain,(
% 3.40/0.81    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl9_12),
% 3.40/0.81    inference(avatar_component_clause,[],[f154])).
% 3.40/0.81  fof(f2609,plain,(
% 3.40/0.81    r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl9_33 | ~spl9_228)),
% 3.40/0.81    inference(resolution,[],[f2556,f370])).
% 3.40/0.81  fof(f370,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) | ~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl9_33),
% 3.40/0.81    inference(avatar_component_clause,[],[f369])).
% 3.40/0.81  fof(f2556,plain,(
% 3.40/0.81    r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) | ~spl9_228),
% 3.40/0.81    inference(avatar_component_clause,[],[f2554])).
% 3.40/0.81  fof(f2580,plain,(
% 3.40/0.81    ~spl9_227),
% 3.40/0.81    inference(avatar_contradiction_clause,[],[f2576])).
% 3.40/0.81  fof(f2576,plain,(
% 3.40/0.81    $false | ~spl9_227),
% 3.40/0.81    inference(resolution,[],[f2568,f198])).
% 3.40/0.81  fof(f198,plain,(
% 3.40/0.81    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.40/0.81    inference(duplicate_literal_removal,[],[f197])).
% 3.40/0.81  fof(f197,plain,(
% 3.40/0.81    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 3.40/0.81    inference(resolution,[],[f89,f88])).
% 3.40/0.81  fof(f88,plain,(
% 3.40/0.81    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f45])).
% 3.40/0.81  fof(f45,plain,(
% 3.40/0.81    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.40/0.81    inference(ennf_transformation,[],[f20])).
% 3.40/0.81  fof(f20,plain,(
% 3.40/0.81    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.40/0.81    inference(unused_predicate_definition_removal,[],[f1])).
% 3.40/0.81  fof(f1,axiom,(
% 3.40/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.40/0.81  fof(f89,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f45])).
% 3.40/0.81  fof(f2568,plain,(
% 3.40/0.81    ( ! [X2] : (~r1_tarski(X2,sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))) ) | ~spl9_227),
% 3.40/0.81    inference(resolution,[],[f2552,f90])).
% 3.40/0.81  fof(f90,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f46])).
% 3.40/0.81  fof(f46,plain,(
% 3.40/0.81    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.40/0.81    inference(ennf_transformation,[],[f9])).
% 3.40/0.81  fof(f9,axiom,(
% 3.40/0.81    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.40/0.81  fof(f2552,plain,(
% 3.40/0.81    ( ! [X4] : (r2_hidden(sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X4)) ) | ~spl9_227),
% 3.40/0.81    inference(avatar_component_clause,[],[f2551])).
% 3.40/0.81  fof(f2551,plain,(
% 3.40/0.81    spl9_227 <=> ! [X4] : r2_hidden(sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X4)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_227])])).
% 3.40/0.81  fof(f2557,plain,(
% 3.40/0.81    spl9_227 | spl9_228 | ~spl9_91),
% 3.40/0.81    inference(avatar_split_clause,[],[f2544,f851,f2554,f2551])).
% 3.40/0.81  fof(f851,plain,(
% 3.40/0.81    spl9_91 <=> ! [X3] : (r2_hidden(sK5(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X3) | r2_lattice3(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).
% 3.40/0.81  fof(f2544,plain,(
% 3.40/0.81    ( ! [X4] : (r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) | r2_hidden(sK5(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X4)) ) | ~spl9_91),
% 3.40/0.81    inference(resolution,[],[f852,f221])).
% 3.40/0.81  fof(f221,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 3.40/0.81    inference(resolution,[],[f84,f58])).
% 3.40/0.81  fof(f58,plain,(
% 3.40/0.81    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.40/0.81    inference(cnf_transformation,[],[f3])).
% 3.40/0.81  fof(f3,axiom,(
% 3.40/0.81    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.40/0.81  fof(f84,plain,(
% 3.40/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f42])).
% 3.40/0.81  fof(f42,plain,(
% 3.40/0.81    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.40/0.81    inference(ennf_transformation,[],[f2])).
% 3.40/0.81  fof(f2,axiom,(
% 3.40/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 3.40/0.81  fof(f852,plain,(
% 3.40/0.81    ( ! [X3] : (r2_hidden(sK5(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X3) | r2_lattice3(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) ) | ~spl9_91),
% 3.40/0.81    inference(avatar_component_clause,[],[f851])).
% 3.40/0.81  fof(f991,plain,(
% 3.40/0.81    spl9_107),
% 3.40/0.81    inference(avatar_contradiction_clause,[],[f990])).
% 3.40/0.81  fof(f990,plain,(
% 3.40/0.81    $false | spl9_107),
% 3.40/0.81    inference(resolution,[],[f977,f229])).
% 3.40/0.81  fof(f229,plain,(
% 3.40/0.81    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.40/0.81    inference(backward_demodulation,[],[f77,f207])).
% 3.40/0.81  fof(f977,plain,(
% 3.40/0.81    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl9_107),
% 3.40/0.81    inference(avatar_component_clause,[],[f975])).
% 3.40/0.81  fof(f975,plain,(
% 3.40/0.81    spl9_107 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).
% 3.40/0.81  fof(f979,plain,(
% 3.40/0.81    spl9_92 | ~spl9_5 | ~spl9_97),
% 3.40/0.81    inference(avatar_split_clause,[],[f970,f895,f116,f855])).
% 3.40/0.81  fof(f855,plain,(
% 3.40/0.81    spl9_92 <=> r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).
% 3.40/0.81  fof(f116,plain,(
% 3.40/0.81    spl9_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 3.40/0.81  fof(f970,plain,(
% 3.40/0.81    r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl9_5 | ~spl9_97)),
% 3.40/0.81    inference(resolution,[],[f897,f222])).
% 3.40/0.81  fof(f222,plain,(
% 3.40/0.81    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,u1_struct_0(sK0))) ) | ~spl9_5),
% 3.40/0.81    inference(resolution,[],[f84,f118])).
% 3.40/0.81  fof(f118,plain,(
% 3.40/0.81    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_5),
% 3.40/0.81    inference(avatar_component_clause,[],[f116])).
% 3.40/0.81  fof(f897,plain,(
% 3.40/0.81    r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | ~spl9_97),
% 3.40/0.81    inference(avatar_component_clause,[],[f895])).
% 3.40/0.81  fof(f978,plain,(
% 3.40/0.81    spl9_19 | ~spl9_92 | ~spl9_107 | ~spl9_5 | ~spl9_97),
% 3.40/0.81    inference(avatar_split_clause,[],[f969,f895,f116,f975,f855,f203])).
% 3.40/0.81  fof(f969,plain,(
% 3.40/0.81    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~spl9_97),
% 3.40/0.81    inference(resolution,[],[f897,f86])).
% 3.40/0.81  fof(f86,plain,(
% 3.40/0.81    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK7(X0,X1,X2),X1) | X1 = X2) )),
% 3.40/0.81    inference(cnf_transformation,[],[f44])).
% 3.40/0.81  fof(f44,plain,(
% 3.40/0.81    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.40/0.81    inference(flattening,[],[f43])).
% 3.40/0.81  fof(f43,plain,(
% 3.40/0.81    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.40/0.81    inference(ennf_transformation,[],[f4])).
% 3.40/0.81  fof(f4,axiom,(
% 3.40/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 3.40/0.81  fof(f853,plain,(
% 3.40/0.81    spl9_91 | ~spl9_1 | ~spl9_59),
% 3.40/0.81    inference(avatar_split_clause,[],[f840,f528,f96,f851])).
% 3.40/0.81  fof(f96,plain,(
% 3.40/0.81    spl9_1 <=> l1_orders_2(sK0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.40/0.81  fof(f840,plain,(
% 3.40/0.81    ( ! [X3] : (~l1_orders_2(sK0) | r2_hidden(sK5(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),X3) | r2_lattice3(sK0,X3,sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) ) | ~spl9_59),
% 3.40/0.81    inference(resolution,[],[f530,f74])).
% 3.40/0.81  fof(f74,plain,(
% 3.40/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f34])).
% 3.40/0.81  fof(f34,plain,(
% 3.40/0.81    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(flattening,[],[f33])).
% 3.40/0.81  fof(f33,plain,(
% 3.40/0.81    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(ennf_transformation,[],[f10])).
% 3.40/0.81  fof(f10,axiom,(
% 3.40/0.81    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 3.40/0.81  fof(f530,plain,(
% 3.40/0.81    m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl9_59),
% 3.40/0.81    inference(avatar_component_clause,[],[f528])).
% 3.40/0.81  fof(f715,plain,(
% 3.40/0.81    spl9_19 | spl9_59 | ~spl9_5),
% 3.40/0.81    inference(avatar_split_clause,[],[f711,f116,f528,f203])).
% 3.40/0.81  fof(f711,plain,(
% 3.40/0.81    m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~spl9_5),
% 3.40/0.81    inference(resolution,[],[f118,f298])).
% 3.40/0.81  fof(f298,plain,(
% 3.40/0.81    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X4)) | m1_subset_1(sK7(X4,X4,X3),X4) | X3 = X4) )),
% 3.40/0.81    inference(resolution,[],[f87,f229])).
% 3.40/0.81  fof(f87,plain,(
% 3.40/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK7(X0,X1,X2),X0) | X1 = X2) )),
% 3.40/0.81    inference(cnf_transformation,[],[f44])).
% 3.40/0.81  fof(f713,plain,(
% 3.40/0.81    ~spl9_6 | spl9_35 | ~spl9_1 | ~spl9_5),
% 3.40/0.81    inference(avatar_split_clause,[],[f699,f116,f96,f383,f121])).
% 3.40/0.81  fof(f121,plain,(
% 3.40/0.81    spl9_6 <=> v13_waybel_0(sK1,sK0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 3.40/0.81  fof(f699,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl9_5),
% 3.40/0.81    inference(resolution,[],[f118,f65])).
% 3.40/0.81  fof(f65,plain,(
% 3.40/0.81    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f30])).
% 3.40/0.81  fof(f30,plain,(
% 3.40/0.81    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(flattening,[],[f29])).
% 3.40/0.81  fof(f29,plain,(
% 3.40/0.81    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(ennf_transformation,[],[f16])).
% 3.40/0.81  fof(f16,axiom,(
% 3.40/0.81    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 3.40/0.81  fof(f371,plain,(
% 3.40/0.81    spl9_33 | ~spl9_1 | ~spl9_1),
% 3.40/0.81    inference(avatar_split_clause,[],[f366,f96,f96,f369])).
% 3.40/0.81  fof(f366,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) ) | ~spl9_1),
% 3.40/0.81    inference(resolution,[],[f93,f158])).
% 3.40/0.81  fof(f158,plain,(
% 3.40/0.81    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) ) | ~spl9_1),
% 3.40/0.81    inference(resolution,[],[f79,f98])).
% 3.40/0.81  fof(f98,plain,(
% 3.40/0.81    l1_orders_2(sK0) | ~spl9_1),
% 3.40/0.81    inference(avatar_component_clause,[],[f96])).
% 3.40/0.81  fof(f79,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 3.40/0.81    inference(cnf_transformation,[],[f37])).
% 3.40/0.81  fof(f37,plain,(
% 3.40/0.81    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(ennf_transformation,[],[f13])).
% 3.40/0.81  fof(f13,axiom,(
% 3.40/0.81    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 3.40/0.81  fof(f93,plain,(
% 3.40/0.81    ( ! [X0,X3,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 3.40/0.81    inference(equality_resolution,[],[f70])).
% 3.40/0.81  fof(f70,plain,(
% 3.40/0.81    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 3.40/0.81    inference(cnf_transformation,[],[f32])).
% 3.40/0.81  fof(f32,plain,(
% 3.40/0.81    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(flattening,[],[f31])).
% 3.40/0.81  fof(f31,plain,(
% 3.40/0.81    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(ennf_transformation,[],[f12])).
% 3.40/0.81  fof(f12,axiom,(
% 3.40/0.81    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 3.40/0.81  fof(f240,plain,(
% 3.40/0.81    spl9_22 | ~spl9_1 | spl9_4 | ~spl9_3 | ~spl9_2),
% 3.40/0.81    inference(avatar_split_clause,[],[f235,f101,f106,f111,f96,f237])).
% 3.40/0.81  fof(f111,plain,(
% 3.40/0.81    spl9_4 <=> v2_struct_0(sK0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 3.40/0.81  fof(f106,plain,(
% 3.40/0.81    spl9_3 <=> v5_orders_2(sK0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 3.40/0.81  fof(f101,plain,(
% 3.40/0.81    spl9_2 <=> v1_yellow_0(sK0)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.40/0.81  fof(f235,plain,(
% 3.40/0.81    ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0) | ~spl9_2),
% 3.40/0.81    inference(resolution,[],[f76,f103])).
% 3.40/0.81  fof(f103,plain,(
% 3.40/0.81    v1_yellow_0(sK0) | ~spl9_2),
% 3.40/0.81    inference(avatar_component_clause,[],[f101])).
% 3.40/0.81  fof(f76,plain,(
% 3.40/0.81    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f36])).
% 3.40/0.81  fof(f36,plain,(
% 3.40/0.81    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.40/0.81    inference(flattening,[],[f35])).
% 3.40/0.81  fof(f35,plain,(
% 3.40/0.81    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.40/0.81    inference(ennf_transformation,[],[f24])).
% 3.40/0.81  fof(f24,plain,(
% 3.40/0.81    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.40/0.81    inference(pure_predicate_removal,[],[f15])).
% 3.40/0.81  fof(f15,axiom,(
% 3.40/0.81    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 3.40/0.81  fof(f220,plain,(
% 3.40/0.81    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 3.40/0.81    introduced(theory_tautology_sat_conflict,[])).
% 3.40/0.81  fof(f206,plain,(
% 3.40/0.81    spl9_8 | spl9_19 | ~spl9_5),
% 3.40/0.81    inference(avatar_split_clause,[],[f200,f116,f203,f131])).
% 3.40/0.81  fof(f200,plain,(
% 3.40/0.81    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl9_5),
% 3.40/0.81    inference(resolution,[],[f82,f118])).
% 3.40/0.81  fof(f180,plain,(
% 3.40/0.81    spl9_15 | spl9_16 | ~spl9_10),
% 3.40/0.81    inference(avatar_split_clause,[],[f162,f142,f177,f173])).
% 3.40/0.81  fof(f173,plain,(
% 3.40/0.81    spl9_15 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 3.40/0.81  fof(f177,plain,(
% 3.40/0.81    spl9_16 <=> v1_xboole_0(u1_struct_0(sK0))),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 3.40/0.81  fof(f162,plain,(
% 3.40/0.81    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl9_10),
% 3.40/0.81    inference(resolution,[],[f81,f144])).
% 3.40/0.81  fof(f144,plain,(
% 3.40/0.81    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl9_10),
% 3.40/0.81    inference(avatar_component_clause,[],[f142])).
% 3.40/0.81  fof(f81,plain,(
% 3.40/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f40])).
% 3.40/0.81  fof(f40,plain,(
% 3.40/0.81    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.40/0.81    inference(flattening,[],[f39])).
% 3.40/0.81  fof(f39,plain,(
% 3.40/0.81    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.40/0.81    inference(ennf_transformation,[],[f7])).
% 3.40/0.81  fof(f7,axiom,(
% 3.40/0.81    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 3.40/0.81  fof(f157,plain,(
% 3.40/0.81    spl9_12 | ~spl9_1),
% 3.40/0.81    inference(avatar_split_clause,[],[f152,f96,f154])).
% 3.40/0.81  fof(f152,plain,(
% 3.40/0.81    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl9_1),
% 3.40/0.81    inference(resolution,[],[f60,f98])).
% 3.40/0.81  fof(f60,plain,(
% 3.40/0.81    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 3.40/0.81    inference(cnf_transformation,[],[f28])).
% 3.40/0.81  fof(f28,plain,(
% 3.40/0.81    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(ennf_transformation,[],[f11])).
% 3.40/0.81  fof(f11,axiom,(
% 3.40/0.81    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 3.40/0.81  fof(f145,plain,(
% 3.40/0.81    spl9_10 | ~spl9_1),
% 3.40/0.81    inference(avatar_split_clause,[],[f140,f96,f142])).
% 3.40/0.81  fof(f140,plain,(
% 3.40/0.81    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl9_1),
% 3.40/0.81    inference(resolution,[],[f59,f98])).
% 3.40/0.81  fof(f59,plain,(
% 3.40/0.81    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))) )),
% 3.40/0.81    inference(cnf_transformation,[],[f27])).
% 3.40/0.81  fof(f27,plain,(
% 3.40/0.81    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.40/0.81    inference(ennf_transformation,[],[f14])).
% 3.40/0.81  fof(f14,axiom,(
% 3.40/0.81    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 3.40/0.81  fof(f139,plain,(
% 3.40/0.81    spl9_8 | ~spl9_9),
% 3.40/0.81    inference(avatar_split_clause,[],[f49,f135,f131])).
% 3.40/0.81  fof(f49,plain,(
% 3.40/0.81    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f26,plain,(
% 3.40/0.81    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.40/0.81    inference(flattening,[],[f25])).
% 3.40/0.81  fof(f25,plain,(
% 3.40/0.81    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.40/0.81    inference(ennf_transformation,[],[f23])).
% 3.40/0.81  fof(f23,plain,(
% 3.40/0.81    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.40/0.81    inference(pure_predicate_removal,[],[f22])).
% 3.40/0.81  fof(f22,plain,(
% 3.40/0.81    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.40/0.81    inference(pure_predicate_removal,[],[f21])).
% 3.40/0.81  fof(f21,plain,(
% 3.40/0.81    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.40/0.81    inference(pure_predicate_removal,[],[f19])).
% 3.40/0.81  fof(f19,negated_conjecture,(
% 3.40/0.81    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.40/0.81    inference(negated_conjecture,[],[f18])).
% 3.40/0.81  fof(f18,conjecture,(
% 3.40/0.81    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.40/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 3.40/0.81  fof(f138,plain,(
% 3.40/0.81    ~spl9_8 | spl9_9),
% 3.40/0.81    inference(avatar_split_clause,[],[f50,f135,f131])).
% 3.40/0.81  fof(f50,plain,(
% 3.40/0.81    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f129,plain,(
% 3.40/0.81    ~spl9_7),
% 3.40/0.81    inference(avatar_split_clause,[],[f51,f126])).
% 3.40/0.81  fof(f126,plain,(
% 3.40/0.81    spl9_7 <=> v1_xboole_0(sK1)),
% 3.40/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 3.40/0.81  fof(f51,plain,(
% 3.40/0.81    ~v1_xboole_0(sK1)),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f124,plain,(
% 3.40/0.81    spl9_6),
% 3.40/0.81    inference(avatar_split_clause,[],[f52,f121])).
% 3.40/0.81  fof(f52,plain,(
% 3.40/0.81    v13_waybel_0(sK1,sK0)),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f119,plain,(
% 3.40/0.81    spl9_5),
% 3.40/0.81    inference(avatar_split_clause,[],[f53,f116])).
% 3.40/0.81  fof(f53,plain,(
% 3.40/0.81    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f114,plain,(
% 3.40/0.81    ~spl9_4),
% 3.40/0.81    inference(avatar_split_clause,[],[f54,f111])).
% 3.40/0.81  fof(f54,plain,(
% 3.40/0.81    ~v2_struct_0(sK0)),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f109,plain,(
% 3.40/0.81    spl9_3),
% 3.40/0.81    inference(avatar_split_clause,[],[f55,f106])).
% 3.40/0.81  fof(f55,plain,(
% 3.40/0.81    v5_orders_2(sK0)),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f104,plain,(
% 3.40/0.81    spl9_2),
% 3.40/0.81    inference(avatar_split_clause,[],[f56,f101])).
% 3.40/0.81  fof(f56,plain,(
% 3.40/0.81    v1_yellow_0(sK0)),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  fof(f99,plain,(
% 3.40/0.81    spl9_1),
% 3.40/0.81    inference(avatar_split_clause,[],[f57,f96])).
% 3.40/0.81  fof(f57,plain,(
% 3.40/0.81    l1_orders_2(sK0)),
% 3.40/0.81    inference(cnf_transformation,[],[f26])).
% 3.40/0.81  % SZS output end Proof for theBenchmark
% 3.40/0.81  % (17916)------------------------------
% 3.40/0.81  % (17916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.81  % (17916)Termination reason: Refutation
% 3.40/0.81  
% 3.40/0.81  % (17916)Memory used [KB]: 13048
% 3.40/0.81  % (17916)Time elapsed: 0.363 s
% 3.40/0.81  % (17916)------------------------------
% 3.40/0.81  % (17916)------------------------------
% 3.40/0.81  % (17899)Success in time 0.449 s
%------------------------------------------------------------------------------
