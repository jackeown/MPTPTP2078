%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1530+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 6.56s
% Output     : Refutation 6.56s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 593 expanded)
%              Number of leaves         :   46 ( 289 expanded)
%              Depth                    :   10
%              Number of atoms          :  961 (4585 expanded)
%              Number of equality atoms :  115 ( 389 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6423,f6424,f6425,f6426,f6427,f6428,f6429,f6430,f6431,f6436,f6441,f6446,f6451,f6611,f6623,f6682,f6699,f6708,f6713,f6718,f6782,f6787,f10376,f10422,f10510,f10629,f12512,f12600,f12617,f13295,f13327,f13330,f13334,f13357,f13358])).

fof(f13358,plain,
    ( spl406_4
    | ~ spl406_6
    | ~ spl406_8
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6794,f6448,f6443,f6438,f6420,f6412])).

fof(f6412,plain,
    ( spl406_4
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_4])])).

fof(f6420,plain,
    ( spl406_6
  <=> r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_6])])).

fof(f6438,plain,
    ( spl406_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_8])])).

fof(f6443,plain,
    ( spl406_9
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_9])])).

fof(f6448,plain,
    ( spl406_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_10])])).

fof(f6794,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl406_6
    | ~ spl406_8
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6440,f5802,f6421,f4273])).

fof(f4273,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3768])).

fof(f3768,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3766,f3767])).

fof(f3767,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3766,plain,(
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
    inference(rectify,[],[f3765])).

fof(f3765,plain,(
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
    inference(nnf_transformation,[],[f2994])).

fof(f2994,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2993])).

fof(f2993,plain,(
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

fof(f6421,plain,
    ( r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl406_6 ),
    inference(avatar_component_clause,[],[f6420])).

fof(f5802,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f5801])).

fof(f5801,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f4346])).

fof(f4346,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3796])).

fof(f3796,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3794,f3795])).

fof(f3795,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3794,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f3793])).

fof(f3793,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f3792])).

fof(f3792,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f6440,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl406_8 ),
    inference(avatar_component_clause,[],[f6438])).

fof(f6445,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl406_9 ),
    inference(avatar_component_clause,[],[f6443])).

fof(f6450,plain,
    ( l1_orders_2(sK0)
    | ~ spl406_10 ),
    inference(avatar_component_clause,[],[f6448])).

fof(f13357,plain,
    ( spl406_1
    | ~ spl406_3
    | ~ spl406_8
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6600,f6448,f6443,f6438,f6408,f6400])).

fof(f6400,plain,
    ( spl406_1
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_1])])).

fof(f6408,plain,
    ( spl406_3
  <=> r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_3])])).

fof(f6600,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl406_3
    | ~ spl406_8
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6440,f5802,f6409,f4296])).

fof(f4296,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3775])).

fof(f3775,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3773,f3774])).

fof(f3774,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3773,plain,(
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
    inference(rectify,[],[f3772])).

fof(f3772,plain,(
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
    inference(nnf_transformation,[],[f3012])).

fof(f3012,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3011])).

fof(f3011,plain,(
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

fof(f6409,plain,
    ( r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl406_3 ),
    inference(avatar_component_clause,[],[f6408])).

fof(f13334,plain,
    ( sK2 != sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | r2_hidden(k4_tarski(sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1),u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f13330,plain,
    ( sK3 != sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | sK1 != sK3
    | r2_lattice3(sK0,k1_tarski(sK4(sK0,k2_tarski(sK2,sK3),sK1)),sK1)
    | ~ r2_lattice3(sK0,k1_tarski(sK3),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f13327,plain,
    ( sK3 != sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | r2_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1)
    | ~ r2_orders_2(sK0,sK3,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f13295,plain,
    ( spl406_607
    | spl406_608
    | ~ spl406_44 ),
    inference(avatar_split_clause,[],[f12886,f6710,f13292,f13288])).

fof(f13288,plain,
    ( spl406_607
  <=> sK3 = sK4(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_607])])).

fof(f13292,plain,
    ( spl406_608
  <=> sK2 = sK4(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_608])])).

fof(f6710,plain,
    ( spl406_44
  <=> r2_hidden(sK4(sK0,k2_tarski(sK2,sK3),sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_44])])).

fof(f12886,plain,
    ( sK2 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | sK3 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl406_44 ),
    inference(resolution,[],[f6712,f5803])).

fof(f5803,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f4345])).

fof(f4345,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3796])).

fof(f6712,plain,
    ( r2_hidden(sK4(sK0,k2_tarski(sK2,sK3),sK1),k2_tarski(sK2,sK3))
    | ~ spl406_44 ),
    inference(avatar_component_clause,[],[f6710])).

fof(f12617,plain,
    ( ~ spl406_548
    | ~ spl406_9
    | ~ spl406_10
    | spl406_43
    | ~ spl406_45 ),
    inference(avatar_split_clause,[],[f12572,f6715,f6705,f6448,f6443,f12612])).

fof(f12612,plain,
    ( spl406_548
  <=> r2_lattice3(sK0,k1_tarski(sK4(sK0,k2_tarski(sK2,sK3),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_548])])).

fof(f6705,plain,
    ( spl406_43
  <=> r1_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_43])])).

fof(f6715,plain,
    ( spl406_45
  <=> m1_subset_1(sK4(sK0,k2_tarski(sK2,sK3),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_45])])).

fof(f12572,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK4(sK0,k2_tarski(sK2,sK3),sK1)),sK1)
    | ~ spl406_9
    | ~ spl406_10
    | spl406_43
    | ~ spl406_45 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f5813,f6707,f6717,f4273])).

fof(f6717,plain,
    ( m1_subset_1(sK4(sK0,k2_tarski(sK2,sK3),sK1),u1_struct_0(sK0))
    | ~ spl406_45 ),
    inference(avatar_component_clause,[],[f6715])).

fof(f6707,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1)
    | spl406_43 ),
    inference(avatar_component_clause,[],[f6705])).

fof(f5813,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f5812])).

fof(f5812,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f4470])).

fof(f4470,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3836])).

fof(f3836,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK18(X0,X1) != X0
            | ~ r2_hidden(sK18(X0,X1),X1) )
          & ( sK18(X0,X1) = X0
            | r2_hidden(sK18(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f3834,f3835])).

fof(f3835,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK18(X0,X1) != X0
          | ~ r2_hidden(sK18(X0,X1),X1) )
        & ( sK18(X0,X1) = X0
          | r2_hidden(sK18(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3834,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f3833])).

fof(f3833,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f12600,plain,
    ( ~ spl406_545
    | ~ spl406_9
    | ~ spl406_10
    | spl406_43
    | ~ spl406_45 ),
    inference(avatar_split_clause,[],[f12577,f6715,f6705,f6448,f6443,f12597])).

fof(f12597,plain,
    ( spl406_545
  <=> r2_hidden(k4_tarski(sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_545])])).

fof(f12577,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1),u1_orders_2(sK0))
    | ~ spl406_9
    | ~ spl406_10
    | spl406_43
    | ~ spl406_45 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6707,f6717,f4292])).

fof(f4292,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3769])).

fof(f3769,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3009])).

fof(f3009,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1885])).

fof(f1885,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f12512,plain,
    ( ~ spl406_539
    | ~ spl406_9
    | ~ spl406_10
    | spl406_43
    | ~ spl406_45 ),
    inference(avatar_split_clause,[],[f12507,f6715,f6705,f6448,f6443,f12509])).

fof(f12509,plain,
    ( spl406_539
  <=> r2_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_539])])).

fof(f12507,plain,
    ( ~ r2_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1)
    | ~ spl406_9
    | ~ spl406_10
    | spl406_43
    | ~ spl406_45 ),
    inference(subsumption_resolution,[],[f12506,f6450])).

fof(f12506,plain,
    ( ~ r2_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl406_9
    | spl406_43
    | ~ spl406_45 ),
    inference(subsumption_resolution,[],[f12505,f6717])).

fof(f12505,plain,
    ( ~ r2_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1)
    | ~ m1_subset_1(sK4(sK0,k2_tarski(sK2,sK3),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl406_9
    | spl406_43 ),
    inference(subsumption_resolution,[],[f12499,f6445])).

fof(f12499,plain,
    ( ~ r2_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k2_tarski(sK2,sK3),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl406_43 ),
    inference(resolution,[],[f6707,f4293])).

fof(f4293,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3771])).

fof(f3771,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3770])).

fof(f3770,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3010])).

fof(f3010,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1864])).

fof(f1864,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f10629,plain,
    ( ~ spl406_1
    | spl406_49
    | ~ spl406_347 ),
    inference(avatar_split_clause,[],[f10511,f10373,f6779,f6400])).

fof(f6779,plain,
    ( spl406_49
  <=> r1_orders_2(sK0,sK1,sK5(sK0,k2_tarski(sK2,sK3),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_49])])).

fof(f10373,plain,
    ( spl406_347
  <=> sK2 = sK5(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_347])])).

fof(f10511,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl406_49
    | ~ spl406_347 ),
    inference(backward_demodulation,[],[f6781,f10375])).

fof(f10375,plain,
    ( sK2 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl406_347 ),
    inference(avatar_component_clause,[],[f10373])).

fof(f6781,plain,
    ( ~ r1_orders_2(sK0,sK1,sK5(sK0,k2_tarski(sK2,sK3),sK1))
    | spl406_49 ),
    inference(avatar_component_clause,[],[f6779])).

fof(f10510,plain,
    ( spl406_5
    | ~ spl406_6
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6793,f6448,f6443,f6433,f6420,f6416])).

fof(f6416,plain,
    ( spl406_5
  <=> r1_orders_2(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_5])])).

fof(f6433,plain,
    ( spl406_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_7])])).

fof(f6793,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ spl406_6
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6435,f5800,f6421,f4273])).

fof(f5800,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f5799])).

fof(f5799,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f4347])).

fof(f4347,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3796])).

fof(f6435,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl406_7 ),
    inference(avatar_component_clause,[],[f6433])).

fof(f10422,plain,
    ( sK3 != sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK5(sK0,k2_tarski(sK2,sK3),sK1))
    | ~ r1_orders_2(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f10376,plain,
    ( spl406_346
    | spl406_347
    | ~ spl406_50 ),
    inference(avatar_split_clause,[],[f9917,f6784,f10373,f10369])).

fof(f10369,plain,
    ( spl406_346
  <=> sK3 = sK5(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_346])])).

fof(f6784,plain,
    ( spl406_50
  <=> r2_hidden(sK5(sK0,k2_tarski(sK2,sK3),sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_50])])).

fof(f9917,plain,
    ( sK2 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | sK3 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl406_50 ),
    inference(resolution,[],[f6786,f5803])).

fof(f6786,plain,
    ( r2_hidden(sK5(sK0,k2_tarski(sK2,sK3),sK1),k2_tarski(sK2,sK3))
    | ~ spl406_50 ),
    inference(avatar_component_clause,[],[f6784])).

fof(f6787,plain,
    ( spl406_50
    | spl406_3
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6775,f6448,f6443,f6408,f6784])).

fof(f6775,plain,
    ( r2_hidden(sK5(sK0,k2_tarski(sK2,sK3),sK1),k2_tarski(sK2,sK3))
    | spl406_3
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6410,f4298])).

fof(f4298,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3775])).

fof(f6410,plain,
    ( ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | spl406_3 ),
    inference(avatar_component_clause,[],[f6408])).

fof(f6782,plain,
    ( ~ spl406_49
    | spl406_3
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6776,f6448,f6443,f6408,f6779])).

fof(f6776,plain,
    ( ~ r1_orders_2(sK0,sK1,sK5(sK0,k2_tarski(sK2,sK3),sK1))
    | spl406_3
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6410,f4299])).

fof(f4299,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3775])).

fof(f6718,plain,
    ( spl406_45
    | spl406_6
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6700,f6448,f6443,f6420,f6715])).

fof(f6700,plain,
    ( m1_subset_1(sK4(sK0,k2_tarski(sK2,sK3),sK1),u1_struct_0(sK0))
    | spl406_6
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6422,f4274])).

fof(f4274,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3768])).

fof(f6422,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | spl406_6 ),
    inference(avatar_component_clause,[],[f6420])).

fof(f6713,plain,
    ( spl406_44
    | spl406_6
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6701,f6448,f6443,f6420,f6710])).

fof(f6701,plain,
    ( r2_hidden(sK4(sK0,k2_tarski(sK2,sK3),sK1),k2_tarski(sK2,sK3))
    | spl406_6
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6422,f4275])).

fof(f4275,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3768])).

fof(f6708,plain,
    ( ~ spl406_43
    | spl406_6
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6702,f6448,f6443,f6420,f6705])).

fof(f6702,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,k2_tarski(sK2,sK3),sK1),sK1)
    | spl406_6
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6422,f4276])).

fof(f4276,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3768])).

fof(f6699,plain,
    ( spl406_41
    | spl406_42
    | ~ spl406_5
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6690,f6448,f6443,f6433,f6416,f6696,f6692])).

fof(f6692,plain,
    ( spl406_41
  <=> r2_orders_2(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_41])])).

fof(f6696,plain,
    ( spl406_42
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_42])])).

fof(f6690,plain,
    ( sK1 = sK3
    | r2_orders_2(sK0,sK3,sK1)
    | ~ spl406_5
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(subsumption_resolution,[],[f6689,f6450])).

fof(f6689,plain,
    ( sK1 = sK3
    | r2_orders_2(sK0,sK3,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl406_5
    | ~ spl406_7
    | ~ spl406_9 ),
    inference(subsumption_resolution,[],[f6688,f6435])).

fof(f6688,plain,
    ( sK1 = sK3
    | r2_orders_2(sK0,sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl406_5
    | ~ spl406_9 ),
    inference(subsumption_resolution,[],[f6669,f6445])).

fof(f6669,plain,
    ( sK1 = sK3
    | r2_orders_2(sK0,sK3,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl406_5 ),
    inference(resolution,[],[f6417,f4295])).

fof(f4295,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | X1 = X2
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3771])).

fof(f6417,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ spl406_5 ),
    inference(avatar_component_clause,[],[f6416])).

fof(f6682,plain,
    ( spl406_39
    | ~ spl406_5
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6667,f6448,f6443,f6433,f6416,f6679])).

fof(f6679,plain,
    ( spl406_39
  <=> r2_lattice3(sK0,k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_39])])).

fof(f6667,plain,
    ( r2_lattice3(sK0,k1_tarski(sK3),sK1)
    | ~ spl406_5
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6445,f6435,f6417,f4280])).

fof(f4280,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2995])).

fof(f2995,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2969])).

fof(f2969,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f6623,plain,
    ( spl406_31
    | ~ spl406_4
    | ~ spl406_8
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_split_clause,[],[f6614,f6448,f6443,f6438,f6412,f6620])).

fof(f6620,plain,
    ( spl406_31
  <=> r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_31])])).

fof(f6614,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl406_4
    | ~ spl406_8
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6440,f6445,f6413,f4291])).

fof(f4291,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3769])).

fof(f6413,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl406_4 ),
    inference(avatar_component_clause,[],[f6412])).

fof(f6611,plain,
    ( spl406_2
    | ~ spl406_3
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(avatar_contradiction_clause,[],[f6610])).

fof(f6610,plain,
    ( $false
    | spl406_2
    | ~ spl406_3
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(subsumption_resolution,[],[f6594,f5800])).

fof(f6594,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK2,sK3))
    | spl406_2
    | ~ spl406_3
    | ~ spl406_7
    | ~ spl406_9
    | ~ spl406_10 ),
    inference(unit_resulting_resolution,[],[f6450,f6435,f6406,f6445,f6409,f4296])).

fof(f6406,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | spl406_2 ),
    inference(avatar_component_clause,[],[f6404])).

fof(f6404,plain,
    ( spl406_2
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_2])])).

fof(f6451,plain,(
    spl406_10 ),
    inference(avatar_split_clause,[],[f4227,f6448])).

fof(f4227,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3764])).

fof(f3764,plain,
    ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
        & r1_orders_2(sK0,sK3,sK1)
        & r1_orders_2(sK0,sK2,sK1) )
      | ( ( ~ r1_orders_2(sK0,sK3,sK1)
          | ~ r1_orders_2(sK0,sK2,sK1) )
        & r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1) )
      | ( ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
        & r1_orders_2(sK0,sK1,sK3)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( ( ~ r1_orders_2(sK0,sK1,sK3)
          | ~ r1_orders_2(sK0,sK1,sK2) )
        & r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2988,f3763,f3762,f3761,f3760])).

fof(f3760,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                        & r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ( ( ~ r1_orders_2(X0,X3,X1)
                          | ~ r1_orders_2(X0,X2,X1) )
                        & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                        & r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( ( ~ r1_orders_2(X0,X1,X3)
                          | ~ r1_orders_2(X0,X1,X2) )
                        & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(sK0,X3,X1)
                      & r1_orders_2(sK0,X2,X1) )
                    | ( ( ~ r1_orders_2(sK0,X3,X1)
                        | ~ r1_orders_2(sK0,X2,X1) )
                      & r2_lattice3(sK0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(sK0,X1,X3)
                      & r1_orders_2(sK0,X1,X2) )
                    | ( ( ~ r1_orders_2(sK0,X1,X3)
                        | ~ r1_orders_2(sK0,X1,X2) )
                      & r1_lattice3(sK0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3761,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),X1)
                    & r1_orders_2(sK0,X3,X1)
                    & r1_orders_2(sK0,X2,X1) )
                  | ( ( ~ r1_orders_2(sK0,X3,X1)
                      | ~ r1_orders_2(sK0,X2,X1) )
                    & r2_lattice3(sK0,k2_tarski(X2,X3),X1) )
                  | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),X1)
                    & r1_orders_2(sK0,X1,X3)
                    & r1_orders_2(sK0,X1,X2) )
                  | ( ( ~ r1_orders_2(sK0,X1,X3)
                      | ~ r1_orders_2(sK0,X1,X2) )
                    & r1_lattice3(sK0,k2_tarski(X2,X3),X1) ) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),sK1)
                  & r1_orders_2(sK0,X3,sK1)
                  & r1_orders_2(sK0,X2,sK1) )
                | ( ( ~ r1_orders_2(sK0,X3,sK1)
                    | ~ r1_orders_2(sK0,X2,sK1) )
                  & r2_lattice3(sK0,k2_tarski(X2,X3),sK1) )
                | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),sK1)
                  & r1_orders_2(sK0,sK1,X3)
                  & r1_orders_2(sK0,sK1,X2) )
                | ( ( ~ r1_orders_2(sK0,sK1,X3)
                    | ~ r1_orders_2(sK0,sK1,X2) )
                  & r1_lattice3(sK0,k2_tarski(X2,X3),sK1) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3762,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),sK1)
                & r1_orders_2(sK0,X3,sK1)
                & r1_orders_2(sK0,X2,sK1) )
              | ( ( ~ r1_orders_2(sK0,X3,sK1)
                  | ~ r1_orders_2(sK0,X2,sK1) )
                & r2_lattice3(sK0,k2_tarski(X2,X3),sK1) )
              | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),sK1)
                & r1_orders_2(sK0,sK1,X3)
                & r1_orders_2(sK0,sK1,X2) )
              | ( ( ~ r1_orders_2(sK0,sK1,X3)
                  | ~ r1_orders_2(sK0,sK1,X2) )
                & r1_lattice3(sK0,k2_tarski(X2,X3),sK1) ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,X3),sK1)
              & r1_orders_2(sK0,X3,sK1)
              & r1_orders_2(sK0,sK2,sK1) )
            | ( ( ~ r1_orders_2(sK0,X3,sK1)
                | ~ r1_orders_2(sK0,sK2,sK1) )
              & r2_lattice3(sK0,k2_tarski(sK2,X3),sK1) )
            | ( ~ r1_lattice3(sK0,k2_tarski(sK2,X3),sK1)
              & r1_orders_2(sK0,sK1,X3)
              & r1_orders_2(sK0,sK1,sK2) )
            | ( ( ~ r1_orders_2(sK0,sK1,X3)
                | ~ r1_orders_2(sK0,sK1,sK2) )
              & r1_lattice3(sK0,k2_tarski(sK2,X3),sK1) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3763,plain,
    ( ? [X3] :
        ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,X3),sK1)
            & r1_orders_2(sK0,X3,sK1)
            & r1_orders_2(sK0,sK2,sK1) )
          | ( ( ~ r1_orders_2(sK0,X3,sK1)
              | ~ r1_orders_2(sK0,sK2,sK1) )
            & r2_lattice3(sK0,k2_tarski(sK2,X3),sK1) )
          | ( ~ r1_lattice3(sK0,k2_tarski(sK2,X3),sK1)
            & r1_orders_2(sK0,sK1,X3)
            & r1_orders_2(sK0,sK1,sK2) )
          | ( ( ~ r1_orders_2(sK0,sK1,X3)
              | ~ r1_orders_2(sK0,sK1,sK2) )
            & r1_lattice3(sK0,k2_tarski(sK2,X3),sK1) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
          & r1_orders_2(sK0,sK3,sK1)
          & r1_orders_2(sK0,sK2,sK1) )
        | ( ( ~ r1_orders_2(sK0,sK3,sK1)
            | ~ r1_orders_2(sK0,sK2,sK1) )
          & r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1) )
        | ( ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
          & r1_orders_2(sK0,sK1,sK3)
          & r1_orders_2(sK0,sK1,sK2) )
        | ( ( ~ r1_orders_2(sK0,sK1,sK3)
            | ~ r1_orders_2(sK0,sK1,sK2) )
          & r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2988,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f2987])).

fof(f2987,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2971])).

fof(f2971,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) )
                       => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) ) )
                      & ( ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) )
                       => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2970])).

fof(f2970,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f6446,plain,(
    spl406_9 ),
    inference(avatar_split_clause,[],[f4228,f6443])).

fof(f4228,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6441,plain,(
    spl406_8 ),
    inference(avatar_split_clause,[],[f4229,f6438])).

fof(f4229,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6436,plain,(
    spl406_7 ),
    inference(avatar_split_clause,[],[f4230,f6433])).

fof(f4230,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6431,plain,
    ( spl406_3
    | spl406_1
    | spl406_6
    | spl406_4 ),
    inference(avatar_split_clause,[],[f4231,f6412,f6420,f6400,f6408])).

fof(f4231,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6430,plain,
    ( spl406_3
    | spl406_2
    | spl406_6
    | spl406_4 ),
    inference(avatar_split_clause,[],[f4233,f6412,f6420,f6404,f6408])).

fof(f4233,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6429,plain,
    ( ~ spl406_1
    | ~ spl406_2
    | ~ spl406_3
    | spl406_6
    | spl406_4 ),
    inference(avatar_split_clause,[],[f4236,f6412,f6420,f6408,f6404,f6400])).

fof(f4236,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6428,plain,
    ( spl406_3
    | spl406_1
    | spl406_6
    | spl406_5 ),
    inference(avatar_split_clause,[],[f4243,f6416,f6420,f6400,f6408])).

fof(f4243,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6427,plain,
    ( spl406_3
    | spl406_2
    | spl406_6
    | spl406_5 ),
    inference(avatar_split_clause,[],[f4245,f6416,f6420,f6404,f6408])).

fof(f4245,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6426,plain,
    ( ~ spl406_1
    | ~ spl406_2
    | ~ spl406_3
    | spl406_6
    | spl406_5 ),
    inference(avatar_split_clause,[],[f4248,f6416,f6420,f6408,f6404,f6400])).

fof(f4248,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6425,plain,
    ( spl406_3
    | spl406_1
    | ~ spl406_4
    | ~ spl406_5
    | ~ spl406_6 ),
    inference(avatar_split_clause,[],[f4261,f6420,f6416,f6412,f6400,f6408])).

fof(f4261,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6424,plain,
    ( spl406_3
    | spl406_2
    | ~ spl406_4
    | ~ spl406_5
    | ~ spl406_6 ),
    inference(avatar_split_clause,[],[f4263,f6420,f6416,f6412,f6404,f6408])).

fof(f4263,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f3764])).

fof(f6423,plain,
    ( ~ spl406_1
    | ~ spl406_2
    | ~ spl406_3
    | ~ spl406_4
    | ~ spl406_5
    | ~ spl406_6 ),
    inference(avatar_split_clause,[],[f4266,f6420,f6416,f6412,f6408,f6404,f6400])).

fof(f4266,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3764])).
%------------------------------------------------------------------------------
