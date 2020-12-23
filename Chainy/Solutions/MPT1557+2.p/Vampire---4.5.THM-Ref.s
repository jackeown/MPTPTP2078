%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1557+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 135 expanded)
%              Number of leaves         :    7 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  196 ( 735 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3971,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3965,f3847])).

fof(f3847,plain,(
    r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f3315,f3318,f3686,f3637])).

fof(f3637,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3337])).

fof(f3337,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3201])).

fof(f3201,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK5(X0,X1,X2))
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3199,f3200])).

fof(f3200,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3199,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3198])).

fof(f3198,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3197])).

fof(f3197,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3047])).

fof(f3047,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3046])).

fof(f3046,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2968])).

fof(f2968,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f3686,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3315,f3323])).

fof(f3323,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3041,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2977])).

fof(f2977,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f3318,plain,(
    r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f3189])).

fof(f3189,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    & r2_yellow_0(sK0,sK2)
    & r2_yellow_0(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3034,f3188,f3187])).

fof(f3187,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
          & r2_yellow_0(sK0,X2)
          & r2_yellow_0(sK0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3188,plain,
    ( ? [X2,X1] :
        ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
        & r2_yellow_0(sK0,X2)
        & r2_yellow_0(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
      & r2_yellow_0(sK0,sK2)
      & r2_yellow_0(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3034,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3033])).

fof(f3033,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3012])).

fof(f3012,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( ( r2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & r1_tarski(X1,X2) )
           => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f3011])).

fof(f3011,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

fof(f3315,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3189])).

fof(f3965,plain,(
    ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f3315,f3316,f3686,f3740,f3416])).

fof(f3416,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f3088,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3019])).

fof(f3019,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f3740,plain,(
    ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f3739,f3315])).

fof(f3739,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3738,f3686])).

fof(f3738,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3737,f3317])).

fof(f3317,plain,(
    r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f3189])).

fof(f3737,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3733,f3686])).

fof(f3733,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3319,f3636])).

fof(f3636,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3338])).

fof(f3338,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3201])).

fof(f3319,plain,(
    ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f3189])).

fof(f3316,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f3189])).
%------------------------------------------------------------------------------
