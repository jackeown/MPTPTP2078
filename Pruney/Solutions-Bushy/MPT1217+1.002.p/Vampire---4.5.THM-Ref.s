%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1217+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:29 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  244 ( 542 expanded)
%              Number of leaves         :   55 ( 253 expanded)
%              Depth                    :    9
%              Number of atoms          : 1061 (2612 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f111,f127,f129,f139,f142,f152,f154,f174,f176,f185,f187,f201,f203,f206,f252,f254,f256,f264,f276,f327,f329,f383,f385,f391,f393,f405,f407,f418,f441,f640,f664,f989,f1190,f1208,f1307,f1383])).

fof(f1383,plain,
    ( ~ spl4_21
    | ~ spl4_41
    | spl4_43
    | ~ spl4_4
    | ~ spl4_117 ),
    inference(avatar_split_clause,[],[f1364,f1183,f125,f415,f398,f240])).

fof(f240,plain,
    ( spl4_21
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f398,plain,
    ( spl4_41
  <=> m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f415,plain,
    ( spl4_43
  <=> k5_lattices(sK1) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f125,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k2_lattices(sK1,X0,X1) = k4_lattices(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1183,plain,
    ( spl4_117
  <=> k5_lattices(sK1) = k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f1364,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_4
    | ~ spl4_117 ),
    inference(superposition,[],[f126,f1185])).

fof(f1185,plain,
    ( k5_lattices(sK1) = k2_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ spl4_117 ),
    inference(avatar_component_clause,[],[f1183])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( k2_lattices(sK1,X0,X1) = k4_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1307,plain,
    ( spl4_2
    | ~ spl4_9
    | ~ spl4_36
    | ~ spl4_1
    | ~ spl4_115
    | spl4_118 ),
    inference(avatar_split_clause,[],[f1305,f1187,f1175,f98,f368,f158,f102])).

fof(f102,plain,
    ( spl4_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f158,plain,
    ( spl4_9
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f368,plain,
    ( spl4_36
  <=> v13_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f98,plain,
    ( spl4_1
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1175,plain,
    ( spl4_115
  <=> m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f1187,plain,
    ( spl4_118
  <=> r3_lattices(sK1,k5_lattices(sK1),k2_lattices(sK1,sK2,k7_lattices(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f1305,plain,
    ( ~ m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v13_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_118 ),
    inference(resolution,[],[f1189,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,k5_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

fof(f1189,plain,
    ( ~ r3_lattices(sK1,k5_lattices(sK1),k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)))
    | spl4_118 ),
    inference(avatar_component_clause,[],[f1187])).

fof(f1208,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_41
    | spl4_115 ),
    inference(avatar_split_clause,[],[f1206,f1175,f398,f240,f133,f102])).

fof(f133,plain,
    ( spl4_5
  <=> l1_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1206,plain,
    ( ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_115 ),
    inference(resolution,[],[f1177,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f1177,plain,
    ( ~ m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | spl4_115 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1190,plain,
    ( ~ spl4_12
    | ~ spl4_115
    | spl4_117
    | ~ spl4_118
    | ~ spl4_17
    | ~ spl4_97 ),
    inference(avatar_split_clause,[],[f1170,f986,f199,f1187,f1183,f1175,f169])).

fof(f169,plain,
    ( spl4_12
  <=> m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f199,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ r3_lattices(sK1,X0,X1)
        | ~ r1_lattices(sK1,X1,X0)
        | X0 = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f986,plain,
    ( spl4_97
  <=> r1_lattices(sK1,k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f1170,plain,
    ( ~ r3_lattices(sK1,k5_lattices(sK1),k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)))
    | k5_lattices(sK1) = k2_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ spl4_17
    | ~ spl4_97 ),
    inference(resolution,[],[f988,f200])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK1,X1,X0)
        | ~ r3_lattices(sK1,X0,X1)
        | X0 = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f199])).

fof(f988,plain,
    ( r1_lattices(sK1,k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1))
    | ~ spl4_97 ),
    inference(avatar_component_clause,[],[f986])).

fof(f989,plain,
    ( ~ spl4_41
    | spl4_97
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f971,f662,f323,f986,f398])).

fof(f323,plain,
    ( spl4_31
  <=> k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f662,plain,
    ( spl4_64
  <=> ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f971,plain,
    ( r1_lattices(sK1,k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(superposition,[],[f663,f325])).

fof(f325,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f323])).

fof(f663,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f662])).

fof(f664,plain,
    ( ~ spl4_30
    | spl4_64
    | ~ spl4_4
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f651,f638,f125,f662,f319])).

fof(f319,plain,
    ( spl4_30
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f638,plain,
    ( spl4_60
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k2_lattices(sK1,sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f651,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1)) )
    | ~ spl4_4
    | ~ spl4_60 ),
    inference(duplicate_literal_removal,[],[f650])).

fof(f650,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1)) )
    | ~ spl4_4
    | ~ spl4_60 ),
    inference(superposition,[],[f639,f126])).

fof(f639,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k2_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f638])).

fof(f640,plain,
    ( spl4_60
    | ~ spl4_30
    | ~ spl4_21
    | ~ spl4_14
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f632,f381,f183,f240,f319,f638])).

fof(f183,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ r3_lattices(sK1,X0,X1)
        | r1_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f381,plain,
    ( spl4_39
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattices(sK1,X0,X1)
        | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f632,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k2_lattices(sK1,sK3,X0)) )
    | ~ spl4_14
    | ~ spl4_39 ),
    inference(resolution,[],[f587,f64])).

fof(f64,plain,(
    r3_lattices(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2))
    & r3_lattices(sK1,sK2,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v17_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f53,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,X1))
              & r3_lattices(sK1,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v17_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,X1))
            & r3_lattices(sK1,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,sK2))
          & r3_lattices(sK1,sK2,X2)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,sK2))
        & r3_lattices(sK1,sK2,X2)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2))
      & r3_lattices(sK1,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

fof(f587,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_lattices(sK1,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattices(sK1,k2_lattices(sK1,X0,X1),k2_lattices(sK1,X2,X1)) )
    | ~ spl4_14
    | ~ spl4_39 ),
    inference(duplicate_literal_removal,[],[f586])).

fof(f586,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK1,k2_lattices(sK1,X0,X1),k2_lattices(sK1,X2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r3_lattices(sK1,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl4_14
    | ~ spl4_39 ),
    inference(resolution,[],[f382,f184])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK1,X0,X1)
        | ~ r3_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f382,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK1,X0,X1)
        | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f381])).

fof(f441,plain,
    ( ~ spl4_22
    | ~ spl4_21
    | spl4_12
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f258,f248,f137,f169,f240,f244])).

fof(f244,plain,
    ( spl4_22
  <=> m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f137,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( m1_subset_1(k4_lattices(sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f248,plain,
    ( spl4_23
  <=> k5_lattices(sK1) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f258,plain,
    ( m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(superposition,[],[f138,f250])).

fof(f250,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK2))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_lattices(sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f418,plain,
    ( ~ spl4_41
    | ~ spl4_43
    | ~ spl4_8
    | spl4_42 ),
    inference(avatar_split_clause,[],[f413,f402,f150,f415,f398])).

fof(f150,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_lattices(sK1,X0,X1) = k4_lattices(sK1,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f402,plain,
    ( spl4_42
  <=> k5_lattices(sK1) = k4_lattices(sK1,k7_lattices(sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f413,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ spl4_8
    | spl4_42 ),
    inference(superposition,[],[f404,f216])).

fof(f216,plain,
    ( ! [X4] :
        ( k4_lattices(sK1,sK2,X4) = k4_lattices(sK1,X4,sK2)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f151,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_lattices(sK1,X0,X1) = k4_lattices(sK1,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f404,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,k7_lattices(sK1,sK3),sK2)
    | spl4_42 ),
    inference(avatar_component_clause,[],[f402])).

fof(f407,plain,
    ( spl4_2
    | ~ spl4_1
    | ~ spl4_30
    | spl4_41 ),
    inference(avatar_split_clause,[],[f406,f398,f319,f98,f102])).

fof(f406,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_41 ),
    inference(resolution,[],[f400,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f400,plain,
    ( ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f398])).

fof(f405,plain,
    ( ~ spl4_21
    | ~ spl4_41
    | ~ spl4_42
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f394,f262,f402,f398,f240])).

fof(f262,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( k4_lattices(sK1,X0,X1) != k5_lattices(sK1)
        | r3_lattices(sK1,X0,k7_lattices(sK1,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f394,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,k7_lattices(sK1,sK3),sK2)
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_24 ),
    inference(resolution,[],[f263,f65])).

fof(f65,plain,(
    ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK1,X0,k7_lattices(sK1,X1))
        | k4_lattices(sK1,X0,X1) != k5_lattices(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f262])).

fof(f393,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_10
    | spl4_40 ),
    inference(avatar_split_clause,[],[f392,f388,f162,f102,f98])).

fof(f162,plain,
    ( spl4_10
  <=> v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f388,plain,
    ( spl4_40
  <=> v15_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f392,plain,
    ( ~ v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl4_40 ),
    inference(resolution,[],[f390,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f390,plain,
    ( ~ v15_lattices(sK1)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f388])).

fof(f391,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_40
    | spl4_36 ),
    inference(avatar_split_clause,[],[f386,f368,f388,f102,f98])).

fof(f386,plain,
    ( ~ v15_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl4_36 ),
    inference(resolution,[],[f370,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).

fof(f370,plain,
    ( ~ v13_lattices(sK1)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f368])).

fof(f385,plain,
    ( ~ spl4_3
    | spl4_38 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl4_3
    | spl4_38 ),
    inference(resolution,[],[f379,f116])).

fof(f116,plain,
    ( v7_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v7_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f108,plain,
    ( sP0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_3
  <=> sP0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f379,plain,
    ( ~ v7_lattices(sK1)
    | spl4_38 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl4_38
  <=> v7_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f383,plain,
    ( spl4_2
    | ~ spl4_38
    | ~ spl4_13
    | ~ spl4_1
    | spl4_39
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f375,f106,f381,f98,f179,f377,f102])).

fof(f179,plain,
    ( spl4_13
  <=> v8_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f375,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
        | ~ v8_lattices(sK1)
        | ~ v7_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f84,f118])).

fof(f118,plain,
    ( v9_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

fof(f329,plain,(
    spl4_30 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl4_30 ),
    inference(resolution,[],[f321,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f321,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f319])).

fof(f327,plain,
    ( spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_30
    | spl4_31
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f316,f274,f323,f319,f98,f162,f158,f102])).

fof(f274,plain,
    ( spl4_25
  <=> ! [X2] :
        ( k4_lattices(sK1,sK3,k7_lattices(sK1,X2)) = k4_lattices(sK1,k7_lattices(sK1,X2),sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f316,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_25 ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl4_25 ),
    inference(superposition,[],[f86,f275])).

fof(f275,plain,
    ( ! [X2] :
        ( k4_lattices(sK1,sK3,k7_lattices(sK1,X2)) = k4_lattices(sK1,k7_lattices(sK1,X2),sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f274])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).

fof(f276,plain,
    ( spl4_2
    | ~ spl4_1
    | spl4_25
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f270,f150,f274,f98,f102])).

fof(f270,plain,
    ( ! [X2] :
        ( k4_lattices(sK1,sK3,k7_lattices(sK1,X2)) = k4_lattices(sK1,k7_lattices(sK1,X2),sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_8 ),
    inference(resolution,[],[f217,f89])).

fof(f217,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK1))
        | k4_lattices(sK1,sK3,X5) = k4_lattices(sK1,X5,sK3) )
    | ~ spl4_8 ),
    inference(resolution,[],[f151,f63])).

fof(f264,plain,
    ( spl4_2
    | ~ spl4_9
    | ~ spl4_1
    | spl4_24 ),
    inference(avatar_split_clause,[],[f260,f262,f98,f158,f102])).

fof(f260,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK1,X0,X1) != k5_lattices(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | r3_lattices(sK1,X0,k7_lattices(sK1,X1))
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f87,f60])).

fof(f60,plain,(
    v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                  | ~ r3_lattices(X0,X1,k7_lattices(X0,X2)) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattices)).

fof(f256,plain,
    ( spl4_2
    | ~ spl4_1
    | ~ spl4_21
    | spl4_22 ),
    inference(avatar_split_clause,[],[f255,f244,f240,f98,f102])).

fof(f255,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_22 ),
    inference(resolution,[],[f246,f89])).

fof(f246,plain,
    ( ~ m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f244])).

fof(f254,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl4_21 ),
    inference(resolution,[],[f242,f62])).

fof(f242,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f240])).

fof(f252,plain,
    ( ~ spl4_22
    | spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_21
    | spl4_23
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f233,f150,f248,f240,f98,f162,f158,f102,f244])).

fof(f233,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | ~ spl4_8 ),
    inference(superposition,[],[f86,f216])).

fof(f206,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f204,f61])).

fof(f61,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f204,plain,
    ( ~ l3_lattices(sK1)
    | spl4_16 ),
    inference(resolution,[],[f197,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f197,plain,
    ( ~ l2_lattices(sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_16
  <=> l2_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f203,plain,
    ( ~ spl4_3
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl4_3
    | spl4_15 ),
    inference(resolution,[],[f193,f113])).

fof(f113,plain,
    ( v4_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f193,plain,
    ( ~ v4_lattices(sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_15
  <=> v4_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f201,plain,
    ( spl4_2
    | ~ spl4_15
    | ~ spl4_16
    | spl4_17
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f189,f183,f199,f195,f191,f102])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | X0 = X1
        | ~ r1_lattices(sK1,X1,X0)
        | ~ l2_lattices(sK1)
        | ~ v4_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | X0 = X1
        | ~ r1_lattices(sK1,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l2_lattices(sK1)
        | ~ v4_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_14 ),
    inference(resolution,[],[f184,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f187,plain,
    ( ~ spl4_3
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl4_3
    | spl4_13 ),
    inference(resolution,[],[f181,f117])).

fof(f117,plain,
    ( v8_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f181,plain,
    ( ~ v8_lattices(sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f179])).

fof(f185,plain,
    ( spl4_2
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_1
    | spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f177,f106,f183,f98,f179,f146,f102])).

fof(f146,plain,
    ( spl4_7
  <=> v6_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | r1_lattices(sK1,X0,X1)
        | ~ v8_lattices(sK1)
        | ~ v6_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f90,f118])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f176,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f164,f60])).

fof(f164,plain,
    ( ~ v17_lattices(sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f174,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f160,f59])).

fof(f59,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f160,plain,
    ( ~ v10_lattices(sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f154,plain,
    ( ~ spl4_3
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl4_3
    | spl4_7 ),
    inference(resolution,[],[f148,f115])).

fof(f115,plain,
    ( v6_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f148,plain,
    ( ~ v6_lattices(sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f152,plain,
    ( spl4_2
    | ~ spl4_7
    | spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f143,f133,f150,f146,f102])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k4_lattices(sK1,X0,X1) = k4_lattices(sK1,X1,X0)
        | ~ v6_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f134,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f134,plain,
    ( l1_lattices(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f142,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f140,f61])).

fof(f140,plain,
    ( ~ l3_lattices(sK1)
    | spl4_5 ),
    inference(resolution,[],[f135,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f135,plain,
    ( ~ l1_lattices(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f139,plain,
    ( spl4_2
    | ~ spl4_5
    | spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f131,f125,f137,f133,f102])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_lattices(sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_lattices(sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f95,f126])).

fof(f129,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f104,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f127,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f123,f106,f125,f102,f98])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k2_lattices(sK1,X0,X1) = k4_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l3_lattices(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f121,f115])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f93,f66])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f111,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f100,f61])).

fof(f100,plain,
    ( ~ l3_lattices(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f109,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f96,f106,f102,f98])).

fof(f96,plain,
    ( sP0(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1) ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f26,f49])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

%------------------------------------------------------------------------------
