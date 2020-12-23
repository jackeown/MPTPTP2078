%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t14_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:10 EDT 2019

% Result     : Theorem 17.07s
% Output     : Refutation 17.07s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 634 expanded)
%              Number of leaves         :   22 ( 203 expanded)
%              Depth                    :   22
%              Number of atoms          :  633 (7354 expanded)
%              Number of equality atoms :   50 ( 592 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2895,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f158,f161,f301,f371,f1130,f2888,f2891,f2894])).

fof(f2894,plain,
    ( ~ spl8_2
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f2893])).

fof(f2893,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f2892,f156])).

fof(f156,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_7
  <=> ~ m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f2892,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f1132,f81])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_tsep_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_tsep_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f61,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_tsep_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_tsep_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_tsep_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_tsep_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | ~ m1_pre_topc(sK1,X0)
              | ~ v1_tsep_1(sK1,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
              | ( m1_pre_topc(sK1,X0)
                & v1_tsep_1(sK1,X0) ) )
            & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_tsep_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK2,X0)
          | ~ v1_tsep_1(sK2,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
        & ( ( m1_pre_topc(sK2,X0)
            & v1_tsep_1(sK2,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',t14_tmap_1)).

fof(f1132,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f141,f1091])).

fof(f1091,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1090,f84])).

fof(f84,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f1090,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f1089,f86])).

fof(f86,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f65])).

fof(f1089,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1088,f85])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f1088,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK2)
      | m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f1087,f86])).

fof(f1087,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1079,f82])).

fof(f82,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f1079,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f1060,f86])).

fof(f1060,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f127,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',dt_m1_pre_topc)).

fof(f127,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',t12_tmap_1)).

fof(f141,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2891,plain,
    ( ~ spl8_1
    | spl8_4
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f2890,f299,f152,f146,f137])).

fof(f137,plain,
    ( spl8_1
  <=> ~ v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f146,plain,
    ( spl8_4
  <=> v1_tsep_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f152,plain,
    ( spl8_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f299,plain,
    ( spl8_16
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK2
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f2890,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f2889,f80])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f2889,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f2874,f81])).

fof(f2874,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(resolution,[],[f2862,f153])).

fof(f153,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f2862,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(sK1,X0) )
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f2861,f1126])).

fof(f1126,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1125,f84])).

fof(f1125,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f1124,f86])).

fof(f1124,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1123,f82])).

fof(f1123,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1113,f83])).

fof(f83,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f1113,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f1100,f86])).

fof(f1100,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f128,f98])).

fof(f128,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f2861,plain,
    ( ! [X0] :
        ( v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ v1_tsep_1(sK1,X0) )
    | ~ spl8_16 ),
    inference(duplicate_literal_removal,[],[f2860])).

fof(f2860,plain,
    ( ! [X0] :
        ( v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ v1_tsep_1(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_16 ),
    inference(resolution,[],[f609,f426])).

fof(f426,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f132,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',t1_tsep_1)).

fof(f132,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',t16_tsep_1)).

fof(f609,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(u1_struct_0(sK1),X2)
        | v1_tsep_1(sK2,X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) )
    | ~ spl8_16 ),
    inference(superposition,[],[f162,f545])).

fof(f545,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_16 ),
    inference(trivial_inequality_removal,[],[f544])).

fof(f544,plain,
    ( sK2 != sK2
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_16 ),
    inference(superposition,[],[f300,f240])).

fof(f240,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2 ),
    inference(subsumption_resolution,[],[f236,f85])).

fof(f236,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f97,f195])).

fof(f195,plain,(
    v1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f194,f83])).

fof(f194,plain,
    ( v1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f187,f86])).

fof(f187,plain,(
    ! [X3] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f114,f96])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',dt_u1_pre_topc)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',dt_g1_pre_topc)).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',abstractness_v1_pre_topc)).

fof(f300,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK2
        | u1_struct_0(sK1) = X0 )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f299])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f99,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f2888,plain,
    ( spl8_0
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f2887,f299,f152,f149,f134])).

fof(f134,plain,
    ( spl8_0
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f149,plain,
    ( spl8_5
  <=> ~ v1_tsep_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f2887,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f2886,f80])).

fof(f2886,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f2880,f81])).

fof(f2880,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(resolution,[],[f2879,f153])).

fof(f2879,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v1_tsep_1(sK1,X0) )
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f2878,f1126])).

fof(f2878,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl8_16 ),
    inference(duplicate_literal_removal,[],[f2875])).

fof(f2875,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_16 ),
    inference(resolution,[],[f612,f162])).

fof(f612,plain,
    ( ! [X3] :
        ( v3_pre_topc(u1_struct_0(sK1),X3)
        | ~ m1_pre_topc(sK2,X3)
        | ~ v1_tsep_1(sK2,X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl8_16 ),
    inference(superposition,[],[f426,f545])).

fof(f1130,plain,
    ( spl8_3
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f1129])).

fof(f1129,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f1128,f81])).

fof(f1128,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f1127,f144])).

fof(f144,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_3
  <=> ~ m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1127,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f1126,f153])).

fof(f371,plain,(
    spl8_15 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f368,f83])).

fof(f368,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_15 ),
    inference(resolution,[],[f297,f96])).

fof(f297,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl8_15
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f301,plain,
    ( ~ spl8_15
    | spl8_16 ),
    inference(avatar_split_clause,[],[f289,f299,f296])).

fof(f289,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK2
      | u1_struct_0(sK1) = X0
      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f116,f86])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t14_tmap_1.p',free_g1_pre_topc)).

fof(f161,plain,
    ( spl8_0
    | spl8_4 ),
    inference(avatar_split_clause,[],[f87,f146,f134])).

fof(f87,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f158,plain,
    ( spl8_2
    | spl8_6 ),
    inference(avatar_split_clause,[],[f90,f152,f140])).

fof(f90,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f157,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f91,f155,f149,f143,f137])).

fof(f91,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
