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
% DateTime   : Thu Dec  3 13:17:42 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 189 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  303 (1489 expanded)
%              Number of equality atoms :   41 ( 179 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f64,f66,f76,f78,f115,f117,f121])).

fof(f121,plain,
    ( ~ spl3_3
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f120,f113,f37,f61])).

fof(f61,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( spl3_1
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f113,plain,
    ( spl3_11
  <=> ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f120,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11 ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,
    ( ! [X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f117,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f24,f106])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_9
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f24,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0) )
    & ( m1_pre_topc(sK2,sK0)
      | m1_pre_topc(sK1,sK0) )
    & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) )
                & ( m1_pre_topc(X2,X0)
                  | m1_pre_topc(X1,X0) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ m1_pre_topc(X1,sK0) )
              & ( m1_pre_topc(X2,sK0)
                | m1_pre_topc(X1,sK0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ m1_pre_topc(X1,sK0) )
            & ( m1_pre_topc(X2,sK0)
              | m1_pre_topc(X1,sK0) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0) )
          & ( m1_pre_topc(X2,sK0)
            | m1_pre_topc(sK1,sK0) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0) )
        & ( m1_pre_topc(X2,sK0)
          | m1_pre_topc(sK1,sK0) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0) )
      & ( m1_pre_topc(sK2,sK0)
        | m1_pre_topc(sK1,sK0) )
      & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                 => ( m1_pre_topc(X1,X0)
                  <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f115,plain,
    ( ~ spl3_9
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f81,f74,f113,f104])).

fof(f74,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK1)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_pre_topc(sK1,X1) )
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( ! [X1] :
        ( sK1 != sK1
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK1)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_pre_topc(sK1,X1) )
    | ~ spl3_5 ),
    inference(superposition,[],[f75,f53])).

fof(f53,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(global_subsumption,[],[f24,f52])).

fof(f52,plain,
    ( sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f51,plain,(
    v1_pre_topc(sK1) ),
    inference(global_subsumption,[],[f26,f25,f47])).

fof(f47,plain,
    ( v1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(superposition,[],[f34,f27])).

fof(f27,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f25,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f78,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f26,f72])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_4
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f76,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f68,f41,f74,f70,f61])).

fof(f41,plain,
    ( spl3_2
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1
        | ~ m1_pre_topc(X0,X1)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X1) )
    | spl3_2 ),
    inference(forward_demodulation,[],[f67,f27])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X1) )
    | spl3_2 ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f42,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f66,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f22,f63])).

fof(f63,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( ~ spl3_3
    | ~ spl3_2
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f59,f41,f41,f61])).

fof(f59,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f50,f45])).

fof(f45,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f29,f43])).

fof(f43,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f29,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X1] :
      ( m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f31,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f44,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f28,f41,f37])).

fof(f28,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (804749313)
% 0.13/0.37  ipcrm: permission denied for id (806092802)
% 0.13/0.37  ipcrm: permission denied for id (804814851)
% 0.13/0.37  ipcrm: permission denied for id (806125572)
% 0.13/0.37  ipcrm: permission denied for id (806158341)
% 0.13/0.37  ipcrm: permission denied for id (804880390)
% 0.13/0.37  ipcrm: permission denied for id (804913159)
% 0.13/0.38  ipcrm: permission denied for id (806191112)
% 0.13/0.38  ipcrm: permission denied for id (809959433)
% 0.13/0.38  ipcrm: permission denied for id (806256650)
% 0.13/0.38  ipcrm: permission denied for id (812515339)
% 0.13/0.38  ipcrm: permission denied for id (806322188)
% 0.13/0.38  ipcrm: permission denied for id (804978701)
% 0.13/0.38  ipcrm: permission denied for id (810024974)
% 0.13/0.38  ipcrm: permission denied for id (805011471)
% 0.13/0.39  ipcrm: permission denied for id (810057744)
% 0.13/0.39  ipcrm: permission denied for id (810090513)
% 0.13/0.39  ipcrm: permission denied for id (806486034)
% 0.13/0.39  ipcrm: permission denied for id (806518803)
% 0.13/0.39  ipcrm: permission denied for id (806584341)
% 0.13/0.39  ipcrm: permission denied for id (806617110)
% 0.13/0.39  ipcrm: permission denied for id (806649879)
% 0.13/0.40  ipcrm: permission denied for id (806682648)
% 0.13/0.40  ipcrm: permission denied for id (810156057)
% 0.13/0.40  ipcrm: permission denied for id (806748186)
% 0.13/0.40  ipcrm: permission denied for id (806780955)
% 0.13/0.40  ipcrm: permission denied for id (806813724)
% 0.13/0.40  ipcrm: permission denied for id (806846493)
% 0.13/0.40  ipcrm: permission denied for id (811466782)
% 0.13/0.40  ipcrm: permission denied for id (810221599)
% 0.13/0.41  ipcrm: permission denied for id (806944800)
% 0.13/0.41  ipcrm: permission denied for id (805109793)
% 0.13/0.41  ipcrm: permission denied for id (806977570)
% 0.13/0.41  ipcrm: permission denied for id (807010339)
% 0.13/0.41  ipcrm: permission denied for id (807043108)
% 0.13/0.41  ipcrm: permission denied for id (807075877)
% 0.13/0.41  ipcrm: permission denied for id (807108646)
% 0.13/0.41  ipcrm: permission denied for id (807174183)
% 0.13/0.42  ipcrm: permission denied for id (807206952)
% 0.13/0.42  ipcrm: permission denied for id (810254377)
% 0.13/0.42  ipcrm: permission denied for id (810287146)
% 0.13/0.42  ipcrm: permission denied for id (807305259)
% 0.13/0.42  ipcrm: permission denied for id (807338028)
% 0.13/0.42  ipcrm: permission denied for id (805208109)
% 0.13/0.42  ipcrm: permission denied for id (807436334)
% 0.13/0.42  ipcrm: permission denied for id (807469103)
% 0.22/0.42  ipcrm: permission denied for id (807501872)
% 0.22/0.43  ipcrm: permission denied for id (810319921)
% 0.22/0.43  ipcrm: permission denied for id (811499570)
% 0.22/0.43  ipcrm: permission denied for id (807632947)
% 0.22/0.43  ipcrm: permission denied for id (807665716)
% 0.22/0.43  ipcrm: permission denied for id (812286005)
% 0.22/0.43  ipcrm: permission denied for id (805339190)
% 0.22/0.43  ipcrm: permission denied for id (807731255)
% 0.22/0.43  ipcrm: permission denied for id (807764024)
% 0.22/0.44  ipcrm: permission denied for id (807796793)
% 0.22/0.44  ipcrm: permission denied for id (807829562)
% 0.22/0.44  ipcrm: permission denied for id (807862331)
% 0.22/0.44  ipcrm: permission denied for id (805470268)
% 0.22/0.44  ipcrm: permission denied for id (805503037)
% 0.22/0.44  ipcrm: permission denied for id (807895102)
% 0.22/0.44  ipcrm: permission denied for id (805568575)
% 0.22/0.44  ipcrm: permission denied for id (807927872)
% 0.22/0.45  ipcrm: permission denied for id (805601345)
% 0.22/0.45  ipcrm: permission denied for id (807960642)
% 0.22/0.45  ipcrm: permission denied for id (807993411)
% 0.22/0.45  ipcrm: permission denied for id (808026180)
% 0.22/0.45  ipcrm: permission denied for id (810418245)
% 0.22/0.45  ipcrm: permission denied for id (808091718)
% 0.22/0.45  ipcrm: permission denied for id (808124487)
% 0.22/0.45  ipcrm: permission denied for id (810451016)
% 0.22/0.46  ipcrm: permission denied for id (810483785)
% 0.22/0.46  ipcrm: permission denied for id (808222794)
% 0.22/0.46  ipcrm: permission denied for id (812318795)
% 0.22/0.46  ipcrm: permission denied for id (808288332)
% 0.22/0.46  ipcrm: permission denied for id (808321101)
% 0.22/0.46  ipcrm: permission denied for id (808353870)
% 0.22/0.46  ipcrm: permission denied for id (811696207)
% 0.22/0.46  ipcrm: permission denied for id (812351568)
% 0.22/0.46  ipcrm: permission denied for id (810614865)
% 0.22/0.47  ipcrm: permission denied for id (810647634)
% 0.22/0.47  ipcrm: permission denied for id (808517715)
% 0.22/0.47  ipcrm: permission denied for id (805765204)
% 0.22/0.47  ipcrm: permission denied for id (811761749)
% 0.22/0.47  ipcrm: permission denied for id (810713174)
% 0.22/0.47  ipcrm: permission denied for id (808616023)
% 0.22/0.47  ipcrm: permission denied for id (805797976)
% 0.22/0.47  ipcrm: permission denied for id (810745945)
% 0.22/0.48  ipcrm: permission denied for id (808681562)
% 0.22/0.48  ipcrm: permission denied for id (808714331)
% 0.22/0.48  ipcrm: permission denied for id (810778716)
% 0.22/0.48  ipcrm: permission denied for id (810811485)
% 0.22/0.48  ipcrm: permission denied for id (808845406)
% 0.22/0.48  ipcrm: permission denied for id (810844255)
% 0.22/0.48  ipcrm: permission denied for id (812580960)
% 0.22/0.48  ipcrm: permission denied for id (808943713)
% 0.22/0.49  ipcrm: permission denied for id (811827298)
% 0.22/0.49  ipcrm: permission denied for id (809042019)
% 0.22/0.49  ipcrm: permission denied for id (809074788)
% 0.22/0.49  ipcrm: permission denied for id (809107557)
% 0.22/0.49  ipcrm: permission denied for id (810942566)
% 0.22/0.49  ipcrm: permission denied for id (812417127)
% 0.22/0.49  ipcrm: permission denied for id (811008104)
% 0.22/0.49  ipcrm: permission denied for id (809238633)
% 0.22/0.50  ipcrm: permission denied for id (809271402)
% 0.22/0.50  ipcrm: permission denied for id (811892843)
% 0.22/0.50  ipcrm: permission denied for id (809336940)
% 0.22/0.50  ipcrm: permission denied for id (811958381)
% 0.22/0.50  ipcrm: permission denied for id (809402478)
% 0.22/0.50  ipcrm: permission denied for id (811991151)
% 0.22/0.50  ipcrm: permission denied for id (809468016)
% 0.22/0.50  ipcrm: permission denied for id (812023921)
% 0.22/0.50  ipcrm: permission denied for id (805929074)
% 0.22/0.51  ipcrm: permission denied for id (812449907)
% 0.22/0.51  ipcrm: permission denied for id (812089460)
% 0.22/0.51  ipcrm: permission denied for id (809599093)
% 0.22/0.51  ipcrm: permission denied for id (809631862)
% 0.22/0.51  ipcrm: permission denied for id (811237495)
% 0.22/0.51  ipcrm: permission denied for id (812122232)
% 0.22/0.51  ipcrm: permission denied for id (809730169)
% 0.22/0.51  ipcrm: permission denied for id (811303034)
% 0.22/0.52  ipcrm: permission denied for id (812155003)
% 0.22/0.52  ipcrm: permission denied for id (805994620)
% 0.22/0.52  ipcrm: permission denied for id (809828477)
% 0.22/0.52  ipcrm: permission denied for id (806027390)
% 0.22/0.52  ipcrm: permission denied for id (809861247)
% 0.76/0.63  % (18721)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.76/0.63  % (18720)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.11/0.64  % (18714)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.11/0.64  % (18732)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.15/0.64  % (18720)Refutation found. Thanks to Tanya!
% 1.15/0.64  % SZS status Theorem for theBenchmark
% 1.15/0.64  % SZS output start Proof for theBenchmark
% 1.15/0.64  fof(f122,plain,(
% 1.15/0.64    $false),
% 1.15/0.64    inference(avatar_sat_refutation,[],[f44,f64,f66,f76,f78,f115,f117,f121])).
% 1.15/0.64  fof(f121,plain,(
% 1.15/0.64    ~spl3_3 | ~spl3_1 | ~spl3_11),
% 1.15/0.64    inference(avatar_split_clause,[],[f120,f113,f37,f61])).
% 1.15/0.64  fof(f61,plain,(
% 1.15/0.64    spl3_3 <=> l1_pre_topc(sK0)),
% 1.15/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.15/0.64  fof(f37,plain,(
% 1.15/0.64    spl3_1 <=> m1_pre_topc(sK1,sK0)),
% 1.15/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.15/0.64  fof(f113,plain,(
% 1.15/0.64    spl3_11 <=> ! [X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.15/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.15/0.64  fof(f120,plain,(
% 1.15/0.64    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_11),
% 1.15/0.64    inference(equality_resolution,[],[f114])).
% 1.15/0.64  fof(f114,plain,(
% 1.15/0.64    ( ! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) ) | ~spl3_11),
% 1.15/0.64    inference(avatar_component_clause,[],[f113])).
% 1.15/0.64  fof(f117,plain,(
% 1.15/0.64    spl3_9),
% 1.15/0.64    inference(avatar_contradiction_clause,[],[f116])).
% 1.15/0.64  fof(f116,plain,(
% 1.15/0.64    $false | spl3_9),
% 1.15/0.64    inference(subsumption_resolution,[],[f24,f106])).
% 1.15/0.64  fof(f106,plain,(
% 1.15/0.64    ~l1_pre_topc(sK1) | spl3_9),
% 1.15/0.64    inference(avatar_component_clause,[],[f104])).
% 1.15/0.64  fof(f104,plain,(
% 1.15/0.64    spl3_9 <=> l1_pre_topc(sK1)),
% 1.15/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.15/0.64  fof(f24,plain,(
% 1.15/0.64    l1_pre_topc(sK1)),
% 1.15/0.64    inference(cnf_transformation,[],[f21])).
% 1.15/0.64  fof(f21,plain,(
% 1.15/0.64    (((~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)) & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 1.15/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19,f18])).
% 1.15/0.64  fof(f18,plain,(
% 1.15/0.64    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) & (m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(X1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0))),
% 1.15/0.64    introduced(choice_axiom,[])).
% 1.15/0.64  fof(f19,plain,(
% 1.15/0.64    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(X1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(sK1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.15/0.64    introduced(choice_axiom,[])).
% 1.15/0.64  fof(f20,plain,(
% 1.15/0.64    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(sK1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)) & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.15/0.64    introduced(choice_axiom,[])).
% 1.15/0.64  fof(f17,plain,(
% 1.15/0.64    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) & (m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.15/0.64    inference(flattening,[],[f16])).
% 1.15/0.64  fof(f16,plain,(
% 1.15/0.64    ? [X0] : (? [X1] : (? [X2] : (((~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) & (m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.15/0.64    inference(nnf_transformation,[],[f8])).
% 1.15/0.64  fof(f8,plain,(
% 1.15/0.64    ? [X0] : (? [X1] : (? [X2] : ((m1_pre_topc(X1,X0) <~> m1_pre_topc(X2,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.15/0.64    inference(flattening,[],[f7])).
% 1.15/0.64  fof(f7,plain,(
% 1.15/0.64    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) <~> m1_pre_topc(X2,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & l1_pre_topc(X0))),
% 1.15/0.64    inference(ennf_transformation,[],[f6])).
% 1.15/0.65  fof(f6,negated_conjecture,(
% 1.15/0.65    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 1.15/0.65    inference(negated_conjecture,[],[f5])).
% 1.15/0.65  fof(f5,conjecture,(
% 1.15/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 1.15/0.65  fof(f115,plain,(
% 1.15/0.65    ~spl3_9 | spl3_11 | ~spl3_5),
% 1.15/0.65    inference(avatar_split_clause,[],[f81,f74,f113,f104])).
% 1.15/0.65  fof(f74,plain,(
% 1.15/0.65    spl3_5 <=> ! [X1,X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1 | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_pre_topc(X0,X1))),
% 1.15/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.15/0.65  fof(f81,plain,(
% 1.15/0.65    ( ! [X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_pre_topc(sK1,X1)) ) | ~spl3_5),
% 1.15/0.65    inference(trivial_inequality_removal,[],[f80])).
% 1.15/0.65  fof(f80,plain,(
% 1.15/0.65    ( ! [X1] : (sK1 != sK1 | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_pre_topc(sK1,X1)) ) | ~spl3_5),
% 1.15/0.65    inference(superposition,[],[f75,f53])).
% 1.15/0.65  fof(f53,plain,(
% 1.15/0.65    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.15/0.65    inference(global_subsumption,[],[f24,f52])).
% 1.15/0.65  fof(f52,plain,(
% 1.15/0.65    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 1.15/0.65    inference(resolution,[],[f51,f33])).
% 1.15/0.65  fof(f33,plain,(
% 1.15/0.65    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f13])).
% 1.15/0.65  fof(f13,plain,(
% 1.15/0.65    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.15/0.65    inference(flattening,[],[f12])).
% 1.15/0.65  fof(f12,plain,(
% 1.15/0.65    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.15/0.65    inference(ennf_transformation,[],[f1])).
% 1.15/0.65  fof(f1,axiom,(
% 1.15/0.65    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.15/0.65  fof(f51,plain,(
% 1.15/0.65    v1_pre_topc(sK1)),
% 1.15/0.65    inference(global_subsumption,[],[f26,f25,f47])).
% 1.15/0.65  fof(f47,plain,(
% 1.15/0.65    v1_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.15/0.65    inference(superposition,[],[f34,f27])).
% 1.15/0.65  fof(f27,plain,(
% 1.15/0.65    sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.15/0.65    inference(cnf_transformation,[],[f21])).
% 1.15/0.65  fof(f34,plain,(
% 1.15/0.65    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f15])).
% 1.15/0.65  fof(f15,plain,(
% 1.15/0.65    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.15/0.65    inference(flattening,[],[f14])).
% 1.15/0.65  fof(f14,plain,(
% 1.15/0.65    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.15/0.65    inference(ennf_transformation,[],[f2])).
% 1.15/0.65  fof(f2,axiom,(
% 1.15/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 1.15/0.65  fof(f25,plain,(
% 1.15/0.65    v2_pre_topc(sK2)),
% 1.15/0.65    inference(cnf_transformation,[],[f21])).
% 1.15/0.65  fof(f26,plain,(
% 1.15/0.65    l1_pre_topc(sK2)),
% 1.15/0.65    inference(cnf_transformation,[],[f21])).
% 1.15/0.65  fof(f75,plain,(
% 1.15/0.65    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1 | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_pre_topc(X0,X1)) ) | ~spl3_5),
% 1.15/0.65    inference(avatar_component_clause,[],[f74])).
% 1.15/0.65  fof(f78,plain,(
% 1.15/0.65    spl3_4),
% 1.15/0.65    inference(avatar_contradiction_clause,[],[f77])).
% 1.15/0.65  fof(f77,plain,(
% 1.15/0.65    $false | spl3_4),
% 1.15/0.65    inference(subsumption_resolution,[],[f26,f72])).
% 1.15/0.65  fof(f72,plain,(
% 1.15/0.65    ~l1_pre_topc(sK2) | spl3_4),
% 1.15/0.65    inference(avatar_component_clause,[],[f70])).
% 1.15/0.65  fof(f70,plain,(
% 1.15/0.65    spl3_4 <=> l1_pre_topc(sK2)),
% 1.15/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.15/0.65  fof(f76,plain,(
% 1.15/0.65    ~spl3_3 | ~spl3_4 | spl3_5 | spl3_2),
% 1.15/0.65    inference(avatar_split_clause,[],[f68,f41,f74,f70,f61])).
% 1.15/0.65  fof(f41,plain,(
% 1.15/0.65    spl3_2 <=> m1_pre_topc(sK2,sK0)),
% 1.15/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.15/0.65  fof(f68,plain,(
% 1.15/0.65    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1 | ~m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1)) ) | spl3_2),
% 1.15/0.65    inference(forward_demodulation,[],[f67,f27])).
% 1.15/0.65  fof(f67,plain,(
% 1.15/0.65    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1)) ) | spl3_2),
% 1.15/0.65    inference(resolution,[],[f42,f32])).
% 1.15/0.65  fof(f32,plain,(
% 1.15/0.65    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f11])).
% 1.15/0.65  fof(f11,plain,(
% 1.15/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.15/0.65    inference(flattening,[],[f10])).
% 1.15/0.65  fof(f10,plain,(
% 1.15/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.15/0.65    inference(ennf_transformation,[],[f3])).
% 1.15/0.65  fof(f3,axiom,(
% 1.15/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
% 1.15/0.65  fof(f42,plain,(
% 1.15/0.65    ~m1_pre_topc(sK2,sK0) | spl3_2),
% 1.15/0.65    inference(avatar_component_clause,[],[f41])).
% 1.15/0.65  fof(f66,plain,(
% 1.15/0.65    spl3_3),
% 1.15/0.65    inference(avatar_contradiction_clause,[],[f65])).
% 1.15/0.65  fof(f65,plain,(
% 1.15/0.65    $false | spl3_3),
% 1.15/0.65    inference(subsumption_resolution,[],[f22,f63])).
% 1.15/0.65  fof(f63,plain,(
% 1.15/0.65    ~l1_pre_topc(sK0) | spl3_3),
% 1.15/0.65    inference(avatar_component_clause,[],[f61])).
% 1.15/0.65  fof(f22,plain,(
% 1.15/0.65    l1_pre_topc(sK0)),
% 1.15/0.65    inference(cnf_transformation,[],[f21])).
% 1.15/0.65  fof(f64,plain,(
% 1.15/0.65    ~spl3_3 | ~spl3_2 | ~spl3_2),
% 1.15/0.65    inference(avatar_split_clause,[],[f59,f41,f41,f61])).
% 1.15/0.65  fof(f59,plain,(
% 1.15/0.65    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~spl3_2),
% 1.15/0.65    inference(resolution,[],[f50,f45])).
% 1.15/0.65  fof(f45,plain,(
% 1.15/0.65    ~m1_pre_topc(sK1,sK0) | ~spl3_2),
% 1.15/0.65    inference(subsumption_resolution,[],[f29,f43])).
% 1.15/0.65  fof(f43,plain,(
% 1.15/0.65    m1_pre_topc(sK2,sK0) | ~spl3_2),
% 1.15/0.65    inference(avatar_component_clause,[],[f41])).
% 1.15/0.65  fof(f29,plain,(
% 1.15/0.65    ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0)),
% 1.15/0.65    inference(cnf_transformation,[],[f21])).
% 1.15/0.65  fof(f50,plain,(
% 1.15/0.65    ( ! [X1] : (m1_pre_topc(sK1,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1)) )),
% 1.15/0.65    inference(superposition,[],[f31,f27])).
% 1.15/0.65  fof(f31,plain,(
% 1.15/0.65    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f9])).
% 1.15/0.65  fof(f9,plain,(
% 1.15/0.65    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.15/0.65    inference(ennf_transformation,[],[f4])).
% 1.15/0.65  fof(f4,axiom,(
% 1.15/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.15/0.65  fof(f44,plain,(
% 1.15/0.65    spl3_1 | spl3_2),
% 1.15/0.65    inference(avatar_split_clause,[],[f28,f41,f37])).
% 1.15/0.65  fof(f28,plain,(
% 1.15/0.65    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 1.15/0.65    inference(cnf_transformation,[],[f21])).
% 1.15/0.65  % SZS output end Proof for theBenchmark
% 1.15/0.65  % (18720)------------------------------
% 1.15/0.65  % (18720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.65  % (18720)Termination reason: Refutation
% 1.15/0.65  
% 1.15/0.65  % (18720)Memory used [KB]: 10618
% 1.15/0.65  % (18720)Time elapsed: 0.068 s
% 1.15/0.65  % (18720)------------------------------
% 1.15/0.65  % (18720)------------------------------
% 1.15/0.65  % (18576)Success in time 0.287 s
%------------------------------------------------------------------------------
