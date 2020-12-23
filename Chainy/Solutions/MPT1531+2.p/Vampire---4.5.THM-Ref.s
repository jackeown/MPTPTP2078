%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1531+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 2.47s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 261 expanded)
%              Number of leaves         :   23 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  410 (1295 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4630,f4635,f4640,f4654,f4674,f4684,f4690,f5085,f5105,f5120,f5140,f5145,f5158,f5194,f5252])).

fof(f5252,plain,
    ( ~ spl180_1
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_5
    | ~ spl180_44
    | spl180_47
    | ~ spl180_48 ),
    inference(avatar_contradiction_clause,[],[f5251])).

fof(f5251,plain,
    ( $false
    | ~ spl180_1
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_5
    | ~ spl180_44
    | spl180_47
    | ~ spl180_48 ),
    inference(subsumption_resolution,[],[f5204,f5124])).

fof(f5124,plain,
    ( r2_hidden(sK7(sK2,sK3,sK5),sK4)
    | ~ spl180_2
    | ~ spl180_44 ),
    inference(unit_resulting_resolution,[],[f4634,f5104,f3747])).

fof(f3747,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3426])).

fof(f3426,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f3424,f3425])).

fof(f3425,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3424,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3423])).

fof(f3423,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3006])).

fof(f3006,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f5104,plain,
    ( r2_hidden(sK7(sK2,sK3,sK5),sK3)
    | ~ spl180_44 ),
    inference(avatar_component_clause,[],[f5102])).

fof(f5102,plain,
    ( spl180_44
  <=> r2_hidden(sK7(sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_44])])).

fof(f4634,plain,
    ( r1_tarski(sK3,sK4)
    | ~ spl180_2 ),
    inference(avatar_component_clause,[],[f4632])).

fof(f4632,plain,
    ( spl180_2
  <=> r1_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_2])])).

fof(f5204,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK5),sK4)
    | ~ spl180_1
    | ~ spl180_3
    | ~ spl180_5
    | spl180_47
    | ~ spl180_48 ),
    inference(unit_resulting_resolution,[],[f4629,f4649,f4639,f5139,f5144,f3715])).

fof(f3715,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f3415])).

fof(f3415,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
                & r2_hidden(sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3413,f3414])).

fof(f3414,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3413,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3412])).

fof(f3412,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2989])).

fof(f2989,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2988])).

fof(f2988,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2831])).

fof(f2831,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f5144,plain,
    ( m1_subset_1(sK7(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ spl180_48 ),
    inference(avatar_component_clause,[],[f5142])).

fof(f5142,plain,
    ( spl180_48
  <=> m1_subset_1(sK7(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_48])])).

fof(f5139,plain,
    ( ~ r1_orders_2(sK2,sK5,sK7(sK2,sK3,sK5))
    | spl180_47 ),
    inference(avatar_component_clause,[],[f5137])).

fof(f5137,plain,
    ( spl180_47
  <=> r1_orders_2(sK2,sK5,sK7(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_47])])).

fof(f4639,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl180_3 ),
    inference(avatar_component_clause,[],[f4637])).

fof(f4637,plain,
    ( spl180_3
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_3])])).

fof(f4649,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ spl180_5 ),
    inference(avatar_component_clause,[],[f4647])).

fof(f4647,plain,
    ( spl180_5
  <=> r1_lattice3(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_5])])).

fof(f4629,plain,
    ( l1_orders_2(sK2)
    | ~ spl180_1 ),
    inference(avatar_component_clause,[],[f4627])).

fof(f4627,plain,
    ( spl180_1
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_1])])).

fof(f5194,plain,
    ( ~ spl180_1
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_6
    | ~ spl180_42
    | ~ spl180_46
    | spl180_49 ),
    inference(avatar_contradiction_clause,[],[f5193])).

fof(f5193,plain,
    ( $false
    | ~ spl180_1
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_6
    | ~ spl180_42
    | ~ spl180_46
    | spl180_49 ),
    inference(subsumption_resolution,[],[f5164,f5086])).

fof(f5086,plain,
    ( r2_hidden(sK6(sK2,sK3,sK5),sK4)
    | ~ spl180_2
    | ~ spl180_42 ),
    inference(unit_resulting_resolution,[],[f4634,f5084,f3747])).

fof(f5084,plain,
    ( r2_hidden(sK6(sK2,sK3,sK5),sK3)
    | ~ spl180_42 ),
    inference(avatar_component_clause,[],[f5082])).

fof(f5082,plain,
    ( spl180_42
  <=> r2_hidden(sK6(sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_42])])).

fof(f5164,plain,
    ( ~ r2_hidden(sK6(sK2,sK3,sK5),sK4)
    | ~ spl180_1
    | ~ spl180_3
    | ~ spl180_6
    | ~ spl180_46
    | spl180_49 ),
    inference(unit_resulting_resolution,[],[f4629,f4653,f4639,f5119,f5157,f3705])).

fof(f3705,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f3411])).

fof(f3411,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3409,f3410])).

fof(f3410,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3409,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3408])).

fof(f3408,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2983])).

fof(f2983,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2982])).

fof(f2982,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2832])).

fof(f2832,axiom,(
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

fof(f5157,plain,
    ( ~ r1_orders_2(sK2,sK6(sK2,sK3,sK5),sK5)
    | spl180_49 ),
    inference(avatar_component_clause,[],[f5155])).

fof(f5155,plain,
    ( spl180_49
  <=> r1_orders_2(sK2,sK6(sK2,sK3,sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_49])])).

fof(f5119,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ spl180_46 ),
    inference(avatar_component_clause,[],[f5117])).

fof(f5117,plain,
    ( spl180_46
  <=> m1_subset_1(sK6(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_46])])).

fof(f4653,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ spl180_6 ),
    inference(avatar_component_clause,[],[f4651])).

fof(f4651,plain,
    ( spl180_6
  <=> r2_lattice3(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_6])])).

fof(f5158,plain,
    ( ~ spl180_49
    | ~ spl180_1
    | ~ spl180_3
    | spl180_12 ),
    inference(avatar_split_clause,[],[f5147,f4681,f4637,f4627,f5155])).

fof(f4681,plain,
    ( spl180_12
  <=> r2_lattice3(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_12])])).

fof(f5147,plain,
    ( ~ r1_orders_2(sK2,sK6(sK2,sK3,sK5),sK5)
    | ~ spl180_1
    | ~ spl180_3
    | spl180_12 ),
    inference(unit_resulting_resolution,[],[f4629,f4639,f4683,f3708])).

fof(f3708,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3411])).

fof(f4683,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | spl180_12 ),
    inference(avatar_component_clause,[],[f4681])).

fof(f5145,plain,
    ( spl180_48
    | ~ spl180_1
    | ~ spl180_3
    | spl180_10 ),
    inference(avatar_split_clause,[],[f5122,f4671,f4637,f4627,f5142])).

fof(f4671,plain,
    ( spl180_10
  <=> r1_lattice3(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_10])])).

fof(f5122,plain,
    ( m1_subset_1(sK7(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ spl180_1
    | ~ spl180_3
    | spl180_10 ),
    inference(unit_resulting_resolution,[],[f4629,f4639,f4673,f3716])).

fof(f3716,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3415])).

fof(f4673,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | spl180_10 ),
    inference(avatar_component_clause,[],[f4671])).

fof(f5140,plain,
    ( ~ spl180_47
    | ~ spl180_1
    | ~ spl180_3
    | spl180_10 ),
    inference(avatar_split_clause,[],[f5121,f4671,f4637,f4627,f5137])).

fof(f5121,plain,
    ( ~ r1_orders_2(sK2,sK5,sK7(sK2,sK3,sK5))
    | ~ spl180_1
    | ~ spl180_3
    | spl180_10 ),
    inference(unit_resulting_resolution,[],[f4629,f4639,f4673,f3718])).

fof(f3718,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3415])).

fof(f5120,plain,
    ( spl180_46
    | ~ spl180_1
    | ~ spl180_3
    | spl180_12 ),
    inference(avatar_split_clause,[],[f4758,f4681,f4637,f4627,f5117])).

fof(f4758,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ spl180_1
    | ~ spl180_3
    | spl180_12 ),
    inference(unit_resulting_resolution,[],[f4629,f4683,f4639,f3706])).

fof(f3706,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3411])).

fof(f5105,plain,
    ( spl180_44
    | ~ spl180_1
    | ~ spl180_3
    | spl180_10 ),
    inference(avatar_split_clause,[],[f4752,f4671,f4637,f4627,f5102])).

fof(f4752,plain,
    ( r2_hidden(sK7(sK2,sK3,sK5),sK3)
    | ~ spl180_1
    | ~ spl180_3
    | spl180_10 ),
    inference(unit_resulting_resolution,[],[f4629,f4673,f4639,f3717])).

fof(f3717,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3415])).

fof(f5085,plain,
    ( spl180_42
    | ~ spl180_1
    | ~ spl180_3
    | spl180_12 ),
    inference(avatar_split_clause,[],[f4750,f4681,f4637,f4627,f5082])).

fof(f4750,plain,
    ( r2_hidden(sK6(sK2,sK3,sK5),sK3)
    | ~ spl180_1
    | ~ spl180_3
    | spl180_12 ),
    inference(unit_resulting_resolution,[],[f4629,f4683,f4639,f3707])).

fof(f3707,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3411])).

fof(f4690,plain,
    ( ~ spl180_10
    | ~ spl180_12 ),
    inference(avatar_split_clause,[],[f3704,f4681,f4671])).

fof(f3704,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f3407])).

fof(f3407,plain,
    ( ( ( ~ r2_lattice3(sK2,sK3,sK5)
        & r2_lattice3(sK2,sK4,sK5) )
      | ( ~ r1_lattice3(sK2,sK3,sK5)
        & r1_lattice3(sK2,sK4,sK5) ) )
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & r1_tarski(sK3,sK4)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f2981,f3406,f3405,f3404])).

fof(f3404,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ( ( ~ r2_lattice3(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3) )
                  | ( ~ r1_lattice3(X0,X1,X3)
                    & r1_lattice3(X0,X2,X3) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(sK2,X1,X3)
                  & r2_lattice3(sK2,X2,X3) )
                | ( ~ r1_lattice3(sK2,X1,X3)
                  & r1_lattice3(sK2,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3405,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ( ( ~ r2_lattice3(sK2,X1,X3)
                & r2_lattice3(sK2,X2,X3) )
              | ( ~ r1_lattice3(sK2,X1,X3)
                & r1_lattice3(sK2,X2,X3) ) )
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & r1_tarski(X1,X2) )
   => ( ? [X3] :
          ( ( ( ~ r2_lattice3(sK2,sK3,X3)
              & r2_lattice3(sK2,sK4,X3) )
            | ( ~ r1_lattice3(sK2,sK3,X3)
              & r1_lattice3(sK2,sK4,X3) ) )
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3406,plain,
    ( ? [X3] :
        ( ( ( ~ r2_lattice3(sK2,sK3,X3)
            & r2_lattice3(sK2,sK4,X3) )
          | ( ~ r1_lattice3(sK2,sK3,X3)
            & r1_lattice3(sK2,sK4,X3) ) )
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ( ( ~ r2_lattice3(sK2,sK3,sK5)
          & r2_lattice3(sK2,sK4,sK5) )
        | ( ~ r1_lattice3(sK2,sK3,sK5)
          & r1_lattice3(sK2,sK4,sK5) ) )
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f2981,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2972])).

fof(f2972,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r2_lattice3(X0,X2,X3)
                   => r2_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                   => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2971])).

fof(f2971,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f4684,plain,
    ( spl180_5
    | ~ spl180_12 ),
    inference(avatar_split_clause,[],[f3703,f4681,f4647])).

fof(f3703,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f3407])).

fof(f4674,plain,
    ( ~ spl180_10
    | spl180_6 ),
    inference(avatar_split_clause,[],[f3702,f4651,f4671])).

fof(f3702,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f3407])).

fof(f4654,plain,
    ( spl180_5
    | spl180_6 ),
    inference(avatar_split_clause,[],[f3701,f4651,f4647])).

fof(f3701,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f3407])).

fof(f4640,plain,(
    spl180_3 ),
    inference(avatar_split_clause,[],[f3700,f4637])).

fof(f3700,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3407])).

fof(f4635,plain,(
    spl180_2 ),
    inference(avatar_split_clause,[],[f3699,f4632])).

fof(f3699,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f3407])).

fof(f4630,plain,(
    spl180_1 ),
    inference(avatar_split_clause,[],[f3698,f4627])).

fof(f3698,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3407])).
%------------------------------------------------------------------------------
