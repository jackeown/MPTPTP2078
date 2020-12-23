%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1580+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:56 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 125 expanded)
%              Number of clauses        :   30 (  33 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 556 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(X0))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ m1_subset_1(sK2,u1_struct_0(X0))
        & m1_subset_1(sK2,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,u1_struct_0(X0))
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_yellow_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,u1_struct_0(X0))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(sK0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26,f25,f24])).

fof(f41,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_354,plain,
    ( l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[status(thm)],[c_4,c_12])).

cnf(c_14,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_356,plain,
    ( l1_orders_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_6,c_9])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_208,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_3,c_5])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_247,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_208,c_13])).

cnf(c_305,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_271,c_247])).

cnf(c_369,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_356,c_305])).

cnf(c_457,plain,
    ( m1_subset_1(X0_42,X1_42)
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | m1_subset_1(X0_42,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_485,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_128,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_127])).

cnf(c_2,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_96,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_4])).

cnf(c_97,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_96])).

cnf(c_344,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[status(thm)],[c_97,c_12])).

cnf(c_346,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_14])).

cnf(c_381,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_128,c_346])).

cnf(c_10,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_485,c_381,c_10,c_11])).


%------------------------------------------------------------------------------
