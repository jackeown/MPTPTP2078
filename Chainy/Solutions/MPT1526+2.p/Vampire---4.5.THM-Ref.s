%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1526+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 979 expanded)
%              Number of leaves         :   10 ( 380 expanded)
%              Depth                    :   59
%              Number of atoms          :  553 (8491 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3269,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3268,f3008])).

fof(f3008,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2991])).

fof(f2991,plain,
    ( ( ( ~ r2_lattice3(sK0,sK3,sK2)
        & r2_lattice3(sK0,sK3,sK1) )
      | ( ~ r1_lattice3(sK0,sK3,sK1)
        & r1_lattice3(sK0,sK3,sK2) ) )
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2976,f2990,f2989,f2988,f2987])).

fof(f2987,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_lattice3(X0,X3,X2)
                      & r2_lattice3(X0,X3,X1) )
                    | ( ~ r1_lattice3(X0,X3,X1)
                      & r1_lattice3(X0,X3,X2) ) )
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(sK0,X3,X2)
                    & r2_lattice3(sK0,X3,X1) )
                  | ( ~ r1_lattice3(sK0,X3,X1)
                    & r1_lattice3(sK0,X3,X2) ) )
              & r1_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2988,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_lattice3(sK0,X3,X2)
                  & r2_lattice3(sK0,X3,X1) )
                | ( ~ r1_lattice3(sK0,X3,X1)
                  & r1_lattice3(sK0,X3,X2) ) )
            & r1_orders_2(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_lattice3(sK0,X3,X2)
                & r2_lattice3(sK0,X3,sK1) )
              | ( ~ r1_lattice3(sK0,X3,sK1)
                & r1_lattice3(sK0,X3,X2) ) )
          & r1_orders_2(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2989,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r2_lattice3(sK0,X3,X2)
              & r2_lattice3(sK0,X3,sK1) )
            | ( ~ r1_lattice3(sK0,X3,sK1)
              & r1_lattice3(sK0,X3,X2) ) )
        & r1_orders_2(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ( ~ r2_lattice3(sK0,X3,sK2)
            & r2_lattice3(sK0,X3,sK1) )
          | ( ~ r1_lattice3(sK0,X3,sK1)
            & r1_lattice3(sK0,X3,sK2) ) )
      & r1_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2990,plain,
    ( ? [X3] :
        ( ( ~ r2_lattice3(sK0,X3,sK2)
          & r2_lattice3(sK0,X3,sK1) )
        | ( ~ r1_lattice3(sK0,X3,sK1)
          & r1_lattice3(sK0,X3,sK2) ) )
   => ( ( ~ r2_lattice3(sK0,sK3,sK2)
        & r2_lattice3(sK0,sK3,sK1) )
      | ( ~ r1_lattice3(sK0,sK3,sK1)
        & r1_lattice3(sK0,sK3,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f2976,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f2975])).

fof(f2975,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2967])).

fof(f2967,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                 => ! [X3] :
                      ( ( r2_lattice3(X0,X3,X1)
                       => r2_lattice3(X0,X3,X2) )
                      & ( r1_lattice3(X0,X3,X2)
                       => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2966])).

fof(f2966,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f3268,plain,(
    ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3267,f3009])).

fof(f3009,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2991])).

fof(f3267,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3265,f3205])).

fof(f3205,plain,(
    ~ r1_lattice3(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f3015,f3202])).

fof(f3202,plain,(
    r2_lattice3(sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f3201,f3008])).

fof(f3201,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3199,f3010])).

fof(f3010,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2991])).

fof(f3199,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f3197])).

fof(f3197,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | r2_lattice3(sK0,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3187,f3019])).

fof(f3019,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2995])).

fof(f2995,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2993,f2994])).

fof(f2994,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2993,plain,(
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
    inference(rectify,[],[f2992])).

fof(f2992,plain,(
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
    inference(nnf_transformation,[],[f2978])).

fof(f2978,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2977])).

fof(f2977,plain,(
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

fof(f3187,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2)
    | r2_lattice3(sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f3186,f3008])).

fof(f3186,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3185,f3010])).

fof(f3185,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f3184])).

fof(f3184,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2)
    | r2_lattice3(sK0,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3144,f3017])).

fof(f3017,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2995])).

fof(f3144,plain,
    ( ~ m1_subset_1(sK4(sK0,sK3,sK2),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK3,sK2)
    | r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2) ),
    inference(resolution,[],[f3125,f3057])).

fof(f3057,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f3056,f3009])).

fof(f3056,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f3055,f3010])).

fof(f3055,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK2) ) ),
    inference(resolution,[],[f3047,f3011])).

fof(f3011,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2991])).

fof(f3047,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f3046,f3008])).

fof(f3046,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_orders_2(sK0,X2,X1) ) ),
    inference(resolution,[],[f3026,f3007])).

fof(f3007,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2991])).

fof(f3026,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f2984])).

fof(f2984,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f2983])).

fof(f2983,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1954])).

fof(f1954,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f3125,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK1)
    | r2_lattice3(sK0,sK3,sK2) ),
    inference(resolution,[],[f3123,f3010])).

fof(f3123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,sK3,X0)
      | r1_orders_2(sK0,sK4(sK0,sK3,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f3122,f3008])).

fof(f3122,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK4(sK0,sK3,X0),sK1)
      | r2_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3121])).

fof(f3121,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK4(sK0,sK3,X0),sK1)
      | r2_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3115,f3017])).

fof(f3115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,sK3,X1),u1_struct_0(sK0))
      | r1_orders_2(sK0,sK4(X0,sK3,X1),sK1)
      | r2_lattice3(X0,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f3114,f3018])).

fof(f3018,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2995])).

fof(f3114,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK1) ) ),
    inference(subsumption_resolution,[],[f3113,f3008])).

fof(f3113,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3110,f3009])).

fof(f3110,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3108,f3016])).

fof(f3016,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2995])).

fof(f3108,plain,(
    r2_lattice3(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f3107,f3013])).

fof(f3013,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | r2_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f2991])).

fof(f3107,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | r2_lattice3(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f3106,f3008])).

fof(f3106,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | r2_lattice3(sK0,sK3,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3104,f3009])).

fof(f3104,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | r2_lattice3(sK0,sK3,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f3102])).

fof(f3102,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | r2_lattice3(sK0,sK3,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK3,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3095,f3025])).

fof(f3025,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2999])).

fof(f2999,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2997,f2998])).

fof(f2998,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2997,plain,(
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
    inference(rectify,[],[f2996])).

fof(f2996,plain,(
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
    inference(nnf_transformation,[],[f2982])).

fof(f2982,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2981])).

fof(f2981,plain,(
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

fof(f3095,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK1,sK5(sK0,sK3,X0))
      | r1_lattice3(sK0,sK3,X0)
      | r2_lattice3(sK0,sK3,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3094,f3009])).

fof(f3094,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK3,X0)
      | r2_lattice3(sK0,sK3,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,sK5(sK0,sK3,X0)) ) ),
    inference(resolution,[],[f3090,f3011])).

fof(f3090,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK3,X0)
      | r2_lattice3(sK0,sK3,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f3089,f3008])).

fof(f3089,plain,(
    ! [X0,X1] :
      ( r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | r2_lattice3(sK0,sK3,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3088])).

fof(f3088,plain,(
    ! [X0,X1] :
      ( r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | r2_lattice3(sK0,sK3,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3075,f3023])).

fof(f3023,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2999])).

fof(f3075,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | r2_lattice3(sK0,sK3,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f3071,f3010])).

fof(f3071,plain,(
    ! [X0,X1] :
      ( r2_lattice3(sK0,sK3,sK1)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0)) ) ),
    inference(resolution,[],[f3065,f3047])).

fof(f3065,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK2,sK5(sK0,sK3,X0))
      | r2_lattice3(sK0,sK3,sK1)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3064,f3008])).

fof(f3064,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK2,sK5(sK0,sK3,X0))
      | r2_lattice3(sK0,sK3,sK1)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3063])).

fof(f3063,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK2,sK5(sK0,sK3,X0))
      | r2_lattice3(sK0,sK3,sK1)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3059,f3023])).

fof(f3059,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK5(X2,sK3,X3),u1_struct_0(sK0))
      | r1_orders_2(sK0,sK2,sK5(X2,sK3,X3))
      | r2_lattice3(sK0,sK3,sK1)
      | r1_lattice3(X2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f3054,f3024])).

fof(f3024,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2999])).

fof(f3054,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK2,X1)
      | r2_lattice3(sK0,sK3,sK1) ) ),
    inference(subsumption_resolution,[],[f3052,f3010])).

fof(f3052,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK2,X1)
      | r2_lattice3(sK0,sK3,sK1) ) ),
    inference(resolution,[],[f3040,f3012])).

fof(f3012,plain,
    ( r1_lattice3(sK0,sK3,sK2)
    | r2_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f2991])).

fof(f3040,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X2,X0) ) ),
    inference(resolution,[],[f3022,f3008])).

fof(f3022,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f2999])).

fof(f3015,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | ~ r2_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f2991])).

fof(f3265,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f3263])).

fof(f3263,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK3,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3256,f3025])).

fof(f3256,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK1,sK5(sK0,sK3,X0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3253,f3009])).

fof(f3253,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,sK5(sK0,sK3,X0)) ) ),
    inference(resolution,[],[f3247,f3011])).

fof(f3247,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f3246,f3008])).

fof(f3246,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3245])).

fof(f3245,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3232,f3023])).

fof(f3232,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f3228,f3010])).

fof(f3228,plain,(
    ! [X0,X1] :
      ( r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK5(sK0,sK3,X0)) ) ),
    inference(resolution,[],[f3222,f3047])).

fof(f3222,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK2,sK5(sK0,sK3,X0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3221,f3008])).

fof(f3221,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK2,sK5(sK0,sK3,X0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3220])).

fof(f3220,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK2,sK5(sK0,sK3,X0))
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_lattice3(sK0,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3214,f3023])).

fof(f3214,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK5(X2,sK3,X3),u1_struct_0(sK0))
      | r1_orders_2(sK0,sK2,sK5(X2,sK3,X3))
      | r1_lattice3(X2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f3203,f3024])).

fof(f3203,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3053,f3202])).

fof(f3053,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK3,sK2)
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3051,f3010])).

fof(f3051,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK2,X0)
      | ~ r2_lattice3(sK0,sK3,sK2) ) ),
    inference(resolution,[],[f3040,f3014])).

fof(f3014,plain,
    ( r1_lattice3(sK0,sK3,sK2)
    | ~ r2_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f2991])).
%------------------------------------------------------------------------------
