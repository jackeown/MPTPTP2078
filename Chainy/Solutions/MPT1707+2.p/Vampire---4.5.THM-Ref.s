%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1707+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 3.38s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  286 (1457 expanded)
%              Number of leaves         :   62 ( 625 expanded)
%              Depth                    :   10
%              Number of atoms          : 1123 (13537 expanded)
%              Number of equality atoms :   56 (2389 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4769,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4487,f4491,f4495,f4499,f4503,f4507,f4511,f4515,f4519,f4523,f4530,f4535,f4542,f4547,f4559,f4564,f4565,f4577,f4578,f4589,f4592,f4594,f4608,f4609,f4611,f4613,f4619,f4621,f4627,f4632,f4635,f4640,f4644,f4646,f4651,f4663,f4668,f4679,f4692,f4706,f4716,f4721,f4723,f4728,f4730,f4731,f4732,f4749,f4760,f4762,f4764,f4766,f4768])).

fof(f4768,plain,
    ( spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(avatar_contradiction_clause,[],[f4767])).

fof(f4767,plain,
    ( $false
    | spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(global_subsumption,[],[f4558,f4576,f4750])).

fof(f4750,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl87_30 ),
    inference(resolution,[],[f4667,f4428])).

fof(f4428,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f3979])).

fof(f3979,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3721])).

fof(f3721,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK19(X0,X1,X2),X1)
              & ~ r2_hidden(sK19(X0,X1,X2),X0) )
            | ~ r2_hidden(sK19(X0,X1,X2),X2) )
          & ( r2_hidden(sK19(X0,X1,X2),X1)
            | r2_hidden(sK19(X0,X1,X2),X0)
            | r2_hidden(sK19(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f3719,f3720])).

fof(f3720,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK19(X0,X1,X2),X1)
            & ~ r2_hidden(sK19(X0,X1,X2),X0) )
          | ~ r2_hidden(sK19(X0,X1,X2),X2) )
        & ( r2_hidden(sK19(X0,X1,X2),X1)
          | r2_hidden(sK19(X0,X1,X2),X0)
          | r2_hidden(sK19(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3719,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f3718])).

fof(f3718,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f3717])).

fof(f3717,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f4667,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_30 ),
    inference(avatar_component_clause,[],[f4666])).

fof(f4666,plain,
    ( spl87_30
  <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_30])])).

fof(f4576,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl87_19 ),
    inference(avatar_component_clause,[],[f4575])).

fof(f4575,plain,
    ( spl87_19
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_19])])).

fof(f4558,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl87_16 ),
    inference(avatar_component_clause,[],[f4557])).

fof(f4557,plain,
    ( spl87_16
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_16])])).

fof(f4766,plain,
    ( spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(avatar_contradiction_clause,[],[f4765])).

fof(f4765,plain,
    ( $false
    | spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(global_subsumption,[],[f4558,f4576,f4750])).

fof(f4764,plain,
    ( spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(avatar_contradiction_clause,[],[f4763])).

fof(f4763,plain,
    ( $false
    | spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(global_subsumption,[],[f4558,f4576,f4750])).

fof(f4762,plain,
    ( spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(avatar_contradiction_clause,[],[f4761])).

fof(f4761,plain,
    ( $false
    | spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(global_subsumption,[],[f4558,f4576,f4750])).

fof(f4760,plain,
    ( spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(avatar_contradiction_clause,[],[f4759])).

fof(f4759,plain,
    ( $false
    | spl87_16
    | spl87_19
    | ~ spl87_30 ),
    inference(global_subsumption,[],[f4558,f4576,f4750])).

fof(f4749,plain,
    ( spl87_25
    | ~ spl87_24
    | ~ spl87_36
    | ~ spl87_23
    | spl87_29 ),
    inference(avatar_split_clause,[],[f4745,f4661,f4600,f4747,f4603,f4606])).

fof(f4606,plain,
    ( spl87_25
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_25])])).

fof(f4603,plain,
    ( spl87_24
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_24])])).

fof(f4747,plain,
    ( spl87_36
  <=> r2_hidden(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_36])])).

fof(f4600,plain,
    ( spl87_23
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_23])])).

fof(f4661,plain,
    ( spl87_29
  <=> r2_hidden(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_29])])).

fof(f4745,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),sK3)
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl87_29 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4744])).

fof(f4744,plain,
    ( ~ r2_hidden(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),sK3)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl87_29 ),
    inference(superposition,[],[f4662,f4418])).

fof(f4418,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3907])).

fof(f3907,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3681])).

fof(f3681,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3365])).

fof(f3365,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3364])).

fof(f3364,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3326])).

fof(f3326,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f4662,plain,
    ( ~ r2_hidden(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),sK3)
    | spl87_29 ),
    inference(avatar_component_clause,[],[f4661])).

fof(f3889,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3678])).

fof(f3678,plain,
    ( ! [X4] :
        ( sK3 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & ! [X5] :
        ( sK3 != X5
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3357,f3677,f3676,f3675,f3674])).

fof(f3674,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3675,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3676,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            & ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3677,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & ! [X5] :
            ( X3 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
   => ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & ! [X5] :
          ( sK3 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3357,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3356])).

fof(f3356,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3350])).

fof(f3350,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f3342])).

fof(f3342,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3341])).

fof(f3341,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f3891,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3678])).

fof(f3892,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3678])).

fof(f3893,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3678])).

fof(f3894,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3678])).

fof(f3895,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3678])).

fof(f4732,plain,
    ( ~ spl87_20
    | ~ spl87_21 ),
    inference(avatar_split_clause,[],[f4657,f4587,f4584])).

fof(f4584,plain,
    ( spl87_20
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_20])])).

fof(f4587,plain,
    ( spl87_21
  <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_21])])).

fof(f4657,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_21 ),
    inference(resolution,[],[f4588,f4156])).

fof(f4156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f3516,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f4588,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_21 ),
    inference(avatar_component_clause,[],[f4587])).

fof(f4731,plain,
    ( ~ spl87_20
    | ~ spl87_21 ),
    inference(avatar_split_clause,[],[f4658,f4587,f4584])).

fof(f4658,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_21 ),
    inference(resolution,[],[f4588,f4170])).

fof(f4170,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3807])).

fof(f3807,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK53(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK53])],[f3805,f3806])).

fof(f3806,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK53(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3805,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f3804])).

fof(f3804,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f4730,plain,
    ( spl87_30
    | ~ spl87_22
    | spl87_28 ),
    inference(avatar_split_clause,[],[f4729,f4638,f4597,f4666])).

fof(f4597,plain,
    ( spl87_22
  <=> m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_22])])).

fof(f4638,plain,
    ( spl87_28
  <=> v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_28])])).

fof(f4729,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_22
    | spl87_28 ),
    inference(global_subsumption,[],[f4727])).

fof(f4727,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_22
    | spl87_28 ),
    inference(global_subsumption,[],[f4650,f4673])).

fof(f4673,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_22 ),
    inference(resolution,[],[f4598,f4159])).

fof(f4159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3521])).

fof(f3521,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f3520])).

fof(f3520,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f4598,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_22 ),
    inference(avatar_component_clause,[],[f4597])).

fof(f4650,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl87_28 ),
    inference(avatar_component_clause,[],[f4638])).

fof(f4728,plain,
    ( spl87_30
    | ~ spl87_22
    | spl87_28 ),
    inference(avatar_split_clause,[],[f4727,f4638,f4597,f4666])).

fof(f4723,plain,
    ( spl87_18
    | ~ spl87_28 ),
    inference(avatar_contradiction_clause,[],[f4722])).

fof(f4722,plain,
    ( $false
    | spl87_18
    | ~ spl87_28 ),
    inference(global_subsumption,[],[f4612,f4718])).

fof(f4718,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl87_28 ),
    inference(resolution,[],[f4639,f4004])).

fof(f4004,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3425])).

fof(f3425,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

fof(f4639,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_28 ),
    inference(avatar_component_clause,[],[f4638])).

fof(f4612,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl87_18 ),
    inference(avatar_component_clause,[],[f4572])).

fof(f4572,plain,
    ( spl87_18
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_18])])).

fof(f4721,plain,
    ( spl87_15
    | ~ spl87_28 ),
    inference(avatar_contradiction_clause,[],[f4720])).

fof(f4720,plain,
    ( $false
    | spl87_15
    | ~ spl87_28 ),
    inference(global_subsumption,[],[f4560,f4717])).

fof(f4717,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl87_28 ),
    inference(resolution,[],[f4639,f4005])).

fof(f4005,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3426])).

fof(f3426,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f4560,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl87_15 ),
    inference(avatar_component_clause,[],[f4554])).

fof(f4554,plain,
    ( spl87_15
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_15])])).

fof(f4716,plain,
    ( spl87_34
    | ~ spl87_35
    | spl87_31 ),
    inference(avatar_split_clause,[],[f4708,f4677,f4714,f4711])).

fof(f4711,plain,
    ( spl87_34
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_34])])).

fof(f4714,plain,
    ( spl87_35
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_35])])).

fof(f4677,plain,
    ( spl87_31
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_31])])).

fof(f4708,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl87_31 ),
    inference(resolution,[],[f4678,f3916])).

fof(f3916,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3687])).

fof(f3687,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3369])).

fof(f3369,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3368])).

fof(f3368,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3345])).

fof(f3345,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f4678,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl87_31 ),
    inference(avatar_component_clause,[],[f4677])).

fof(f4706,plain,
    ( ~ spl87_33
    | spl87_25
    | spl87_2
    | ~ spl87_3
    | ~ spl87_13 ),
    inference(avatar_split_clause,[],[f4694,f4540,f4493,f4489,f4606,f4704])).

fof(f4704,plain,
    ( spl87_33
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_33])])).

fof(f4489,plain,
    ( spl87_2
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_2])])).

fof(f4493,plain,
    ( spl87_3
  <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_3])])).

fof(f4540,plain,
    ( spl87_13
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_13])])).

fof(f4694,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK1)
    | spl87_2
    | ~ spl87_3
    | ~ spl87_13 ),
    inference(resolution,[],[f4570,f4494])).

fof(f4494,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_3 ),
    inference(avatar_component_clause,[],[f4493])).

fof(f4570,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1) )
    | spl87_2
    | ~ spl87_13 ),
    inference(global_subsumption,[],[f3892,f4541,f4566])).

fof(f4566,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | spl87_2 ),
    inference(resolution,[],[f4490,f3920])).

fof(f3920,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3375])).

fof(f3375,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3374])).

fof(f3374,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1846])).

fof(f1846,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f4490,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl87_2 ),
    inference(avatar_component_clause,[],[f4489])).

fof(f4541,plain,
    ( l1_pre_topc(sK1)
    | ~ spl87_13 ),
    inference(avatar_component_clause,[],[f4540])).

fof(f4692,plain,
    ( ~ spl87_32
    | spl87_25
    | spl87_1
    | ~ spl87_3
    | ~ spl87_11 ),
    inference(avatar_split_clause,[],[f4680,f4528,f4493,f4485,f4606,f4690])).

fof(f4690,plain,
    ( spl87_32
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_32])])).

fof(f4485,plain,
    ( spl87_1
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_1])])).

fof(f4528,plain,
    ( spl87_11
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_11])])).

fof(f4680,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK2)
    | spl87_1
    | ~ spl87_3
    | ~ spl87_11 ),
    inference(resolution,[],[f4552,f4494])).

fof(f4552,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2) )
    | spl87_1
    | ~ spl87_11 ),
    inference(global_subsumption,[],[f3894,f4529,f4548])).

fof(f4548,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl87_1 ),
    inference(resolution,[],[f4486,f3920])).

fof(f4486,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl87_1 ),
    inference(avatar_component_clause,[],[f4485])).

fof(f4529,plain,
    ( l1_pre_topc(sK2)
    | ~ spl87_11 ),
    inference(avatar_component_clause,[],[f4528])).

fof(f4679,plain,
    ( ~ spl87_31
    | ~ spl87_22 ),
    inference(avatar_split_clause,[],[f4675,f4597,f4677])).

fof(f4675,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl87_22 ),
    inference(global_subsumption,[],[f4416,f4674])).

fof(f4674,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl87_22 ),
    inference(superposition,[],[f4598,f4003])).

fof(f4003,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3424])).

fof(f3424,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f4416,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f3898])).

fof(f3898,plain,(
    ! [X4] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f3678])).

fof(f4668,plain,
    ( spl87_30
    | spl87_25
    | ~ spl87_23
    | ~ spl87_24
    | ~ spl87_21 ),
    inference(avatar_split_clause,[],[f4664,f4587,f4603,f4600,f4606,f4666])).

fof(f4664,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_21 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4659])).

fof(f4659,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl87_21 ),
    inference(superposition,[],[f4588,f4418])).

fof(f4663,plain,
    ( ~ spl87_29
    | ~ spl87_21 ),
    inference(avatar_split_clause,[],[f4656,f4587,f4661])).

fof(f4656,plain,
    ( ~ r2_hidden(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),sK3)
    | ~ spl87_21 ),
    inference(resolution,[],[f4588,f4092])).

fof(f4092,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3468])).

fof(f3468,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f4651,plain,
    ( ~ spl87_23
    | spl87_25
    | ~ spl87_28
    | ~ spl87_24
    | spl87_20 ),
    inference(avatar_split_clause,[],[f4649,f4584,f4603,f4638,f4606,f4600])).

fof(f4649,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl87_20 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4648])).

fof(f4648,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl87_20 ),
    inference(superposition,[],[f4591,f4418])).

fof(f4591,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl87_20 ),
    inference(avatar_component_clause,[],[f4584])).

fof(f4646,plain,(
    ~ spl87_25 ),
    inference(avatar_contradiction_clause,[],[f4645])).

fof(f4645,plain,
    ( $false
    | ~ spl87_25 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3890,f3889,f4642])).

fof(f4642,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl87_25 ),
    inference(resolution,[],[f4607,f3900])).

fof(f3900,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3359])).

fof(f3359,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3358])).

fof(f3358,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3329])).

fof(f3329,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f4607,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl87_25 ),
    inference(avatar_component_clause,[],[f4606])).

fof(f3890,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3678])).

fof(f4644,plain,(
    ~ spl87_25 ),
    inference(avatar_contradiction_clause,[],[f4643])).

fof(f4643,plain,
    ( $false
    | ~ spl87_25 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4641])).

fof(f4641,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl87_25 ),
    inference(resolution,[],[f4607,f3903])).

fof(f3903,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3361])).

fof(f3361,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3360])).

fof(f3360,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3328])).

fof(f3328,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f4640,plain,
    ( spl87_28
    | ~ spl87_23
    | ~ spl87_24
    | spl87_25
    | ~ spl87_20 ),
    inference(avatar_split_clause,[],[f4636,f4584,f4606,f4603,f4600,f4638])).

fof(f4636,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_20 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4623])).

fof(f4623,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl87_20 ),
    inference(superposition,[],[f4585,f4418])).

fof(f4585,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_20 ),
    inference(avatar_component_clause,[],[f4584])).

fof(f4635,plain,(
    spl87_23 ),
    inference(avatar_contradiction_clause,[],[f4634])).

fof(f4634,plain,
    ( $false
    | spl87_23 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4633])).

fof(f4633,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl87_23 ),
    inference(resolution,[],[f4601,f3905])).

fof(f3905,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3361])).

fof(f4601,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl87_23 ),
    inference(avatar_component_clause,[],[f4600])).

fof(f4632,plain,
    ( ~ spl87_27
    | spl87_26 ),
    inference(avatar_split_clause,[],[f4628,f4625,f4630])).

fof(f4630,plain,
    ( spl87_27
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_27])])).

fof(f4625,plain,
    ( spl87_26
  <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_26])])).

fof(f4628,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl87_26 ),
    inference(resolution,[],[f4626,f4362])).

fof(f4362,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3635])).

fof(f3635,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4626,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl87_26 ),
    inference(avatar_component_clause,[],[f4625])).

fof(f4627,plain,
    ( spl87_25
    | ~ spl87_26
    | ~ spl87_20 ),
    inference(avatar_split_clause,[],[f4622,f4584,f4625,f4606])).

fof(f4622,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl87_20 ),
    inference(resolution,[],[f4585,f4360])).

fof(f4360,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3633])).

fof(f3633,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3632])).

fof(f3632,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f4621,plain,(
    spl87_24 ),
    inference(avatar_contradiction_clause,[],[f4620])).

fof(f4620,plain,
    ( $false
    | spl87_24 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3890,f3889,f4617])).

fof(f4617,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl87_24 ),
    inference(resolution,[],[f4604,f3901])).

fof(f3901,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3359])).

fof(f4604,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl87_24 ),
    inference(avatar_component_clause,[],[f4603])).

fof(f4619,plain,(
    spl87_24 ),
    inference(avatar_contradiction_clause,[],[f4618])).

fof(f4618,plain,
    ( $false
    | spl87_24 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4616])).

fof(f4616,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl87_24 ),
    inference(resolution,[],[f4604,f3904])).

fof(f3904,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3361])).

fof(f4613,plain,
    ( ~ spl87_18
    | ~ spl87_17
    | spl87_2 ),
    inference(avatar_split_clause,[],[f4568,f4489,f4562,f4572])).

fof(f4562,plain,
    ( spl87_17
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_17])])).

fof(f4568,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | spl87_2 ),
    inference(resolution,[],[f4490,f4167])).

fof(f4167,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3801])).

fof(f3801,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3526])).

fof(f3526,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f4611,plain,
    ( ~ spl87_20
    | spl87_17
    | ~ spl87_3 ),
    inference(avatar_split_clause,[],[f4580,f4493,f4562,f4584])).

fof(f4580,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_3 ),
    inference(resolution,[],[f4494,f4166])).

fof(f4166,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3801])).

fof(f4609,plain,
    ( spl87_21
    | spl87_20
    | ~ spl87_3 ),
    inference(avatar_split_clause,[],[f4581,f4493,f4584,f4587])).

fof(f4581,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_3 ),
    inference(resolution,[],[f4494,f4159])).

fof(f4608,plain,
    ( spl87_22
    | ~ spl87_23
    | ~ spl87_24
    | spl87_25
    | ~ spl87_3 ),
    inference(avatar_split_clause,[],[f4595,f4493,f4606,f4603,f4600,f4597])).

fof(f4595,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl87_3 ),
    inference(global_subsumption,[],[f3895,f3894,f3893,f3892,f3891,f3889,f4582])).

fof(f4582,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl87_3 ),
    inference(superposition,[],[f4494,f4418])).

fof(f4594,plain,
    ( spl87_21
    | ~ spl87_3
    | spl87_17 ),
    inference(avatar_split_clause,[],[f4593,f4562,f4493,f4587])).

fof(f4593,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_3
    | spl87_17 ),
    inference(global_subsumption,[],[f4590,f4581])).

fof(f4590,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_3
    | spl87_17 ),
    inference(global_subsumption,[],[f4563,f4580])).

fof(f4563,plain,
    ( ~ v1_xboole_0(sK3)
    | spl87_17 ),
    inference(avatar_component_clause,[],[f4562])).

fof(f4592,plain,
    ( ~ spl87_20
    | ~ spl87_3
    | spl87_17 ),
    inference(avatar_split_clause,[],[f4590,f4562,f4493,f4584])).

fof(f4589,plain,
    ( spl87_20
    | spl87_21
    | ~ spl87_3 ),
    inference(avatar_split_clause,[],[f4579,f4493,f4587,f4584])).

fof(f4579,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl87_3 ),
    inference(resolution,[],[f4494,f4164])).

fof(f4164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3801])).

fof(f4578,plain,
    ( ~ spl87_19
    | spl87_2 ),
    inference(avatar_split_clause,[],[f4569,f4489,f4575])).

fof(f4569,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl87_2 ),
    inference(resolution,[],[f4490,f4091])).

fof(f4091,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3467])).

fof(f3467,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f4577,plain,
    ( spl87_18
    | ~ spl87_19
    | spl87_2 ),
    inference(avatar_split_clause,[],[f4567,f4489,f4575,f4572])).

fof(f4567,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl87_2 ),
    inference(resolution,[],[f4490,f4165])).

fof(f4165,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3801])).

fof(f4565,plain,
    ( ~ spl87_16
    | spl87_1 ),
    inference(avatar_split_clause,[],[f4551,f4485,f4557])).

fof(f4551,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl87_1 ),
    inference(resolution,[],[f4486,f4091])).

fof(f4564,plain,
    ( ~ spl87_15
    | ~ spl87_17
    | spl87_1 ),
    inference(avatar_split_clause,[],[f4550,f4485,f4562,f4554])).

fof(f4550,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | spl87_1 ),
    inference(resolution,[],[f4486,f4167])).

fof(f4559,plain,
    ( spl87_15
    | ~ spl87_16
    | spl87_1 ),
    inference(avatar_split_clause,[],[f4549,f4485,f4557,f4554])).

fof(f4549,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl87_1 ),
    inference(resolution,[],[f4486,f4165])).

fof(f4547,plain,
    ( spl87_14
    | ~ spl87_6 ),
    inference(avatar_split_clause,[],[f4543,f4505,f4545])).

fof(f4545,plain,
    ( spl87_14
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_14])])).

fof(f4505,plain,
    ( spl87_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_6])])).

fof(f4543,plain,
    ( v2_pre_topc(sK1)
    | ~ spl87_6 ),
    inference(global_subsumption,[],[f3891,f3890,f4537])).

fof(f4537,plain,
    ( v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl87_6 ),
    inference(resolution,[],[f4506,f3917])).

fof(f3917,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3371])).

fof(f3371,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3370])).

fof(f3370,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f1760,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f4506,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl87_6 ),
    inference(avatar_component_clause,[],[f4505])).

fof(f4542,plain,
    ( spl87_13
    | ~ spl87_6 ),
    inference(avatar_split_clause,[],[f4538,f4505,f4540])).

fof(f4538,plain,
    ( l1_pre_topc(sK1)
    | ~ spl87_6 ),
    inference(global_subsumption,[],[f3891,f4536])).

fof(f4536,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl87_6 ),
    inference(resolution,[],[f4506,f3935])).

fof(f3935,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4535,plain,
    ( spl87_12
    | ~ spl87_4 ),
    inference(avatar_split_clause,[],[f4531,f4497,f4533])).

fof(f4533,plain,
    ( spl87_12
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_12])])).

fof(f4497,plain,
    ( spl87_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_4])])).

fof(f4531,plain,
    ( v2_pre_topc(sK2)
    | ~ spl87_4 ),
    inference(global_subsumption,[],[f3891,f3890,f4525])).

fof(f4525,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl87_4 ),
    inference(resolution,[],[f4498,f3917])).

fof(f4498,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl87_4 ),
    inference(avatar_component_clause,[],[f4497])).

fof(f4530,plain,
    ( spl87_11
    | ~ spl87_4 ),
    inference(avatar_split_clause,[],[f4526,f4497,f4528])).

fof(f4526,plain,
    ( l1_pre_topc(sK2)
    | ~ spl87_4 ),
    inference(global_subsumption,[],[f3891,f4524])).

fof(f4524,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl87_4 ),
    inference(resolution,[],[f4498,f3935])).

fof(f4523,plain,(
    ~ spl87_10 ),
    inference(avatar_split_clause,[],[f3889,f4521])).

fof(f4521,plain,
    ( spl87_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_10])])).

fof(f4519,plain,(
    spl87_9 ),
    inference(avatar_split_clause,[],[f3890,f4517])).

fof(f4517,plain,
    ( spl87_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_9])])).

fof(f4515,plain,(
    spl87_8 ),
    inference(avatar_split_clause,[],[f3891,f4513])).

fof(f4513,plain,
    ( spl87_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_8])])).

fof(f4511,plain,(
    ~ spl87_7 ),
    inference(avatar_split_clause,[],[f3892,f4509])).

fof(f4509,plain,
    ( spl87_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_7])])).

fof(f4507,plain,(
    spl87_6 ),
    inference(avatar_split_clause,[],[f3893,f4505])).

fof(f4503,plain,(
    ~ spl87_5 ),
    inference(avatar_split_clause,[],[f3894,f4501])).

fof(f4501,plain,
    ( spl87_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_5])])).

fof(f4499,plain,(
    spl87_4 ),
    inference(avatar_split_clause,[],[f3895,f4497])).

fof(f4495,plain,(
    spl87_3 ),
    inference(avatar_split_clause,[],[f3896,f4493])).

fof(f3896,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f3678])).

fof(f4491,plain,(
    ~ spl87_2 ),
    inference(avatar_split_clause,[],[f4417,f4489])).

fof(f4417,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f3897])).

fof(f3897,plain,(
    ! [X5] :
      ( sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f3678])).

fof(f4487,plain,(
    ~ spl87_1 ),
    inference(avatar_split_clause,[],[f4416,f4485])).
%------------------------------------------------------------------------------
