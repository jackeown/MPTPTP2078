%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1921+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:53 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 142 expanded)
%              Number of clauses        :   28 (  38 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 559 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
          & m1_yellow_6(X2,X0,X1) )
     => ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X1))
        & m1_yellow_6(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
     => ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK1))
            & m1_yellow_6(X2,X0,sK1) )
        & l1_waybel_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    & m1_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19,f18,f17])).

fof(f31,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_69,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_7])).

cnf(c_11,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_154,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_69,c_11])).

cnf(c_155,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | m1_yellow_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_154])).

cnf(c_250,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | m1_yellow_0(X1,X0)
    | sK0 != sK0
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_155])).

cnf(c_251,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | m1_yellow_0(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_10,negated_conjecture,
    ( l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_253,plain,
    ( m1_yellow_0(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_251,c_10])).

cnf(c_294,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_253])).

cnf(c_295,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_6,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_182,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_183,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_169,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_170,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | l1_waybel_0(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_239,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | l1_waybel_0(X1,sK0)
    | sK0 != sK0
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_170])).

cnf(c_240,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | l1_waybel_0(sK2,sK0) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_242,plain,
    ( l1_waybel_0(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_240,c_10])).

cnf(c_281,plain,
    ( l1_orders_2(X0)
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_183,c_242])).

cnf(c_282,plain,
    ( l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_274,plain,
    ( l1_orders_2(X0)
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_183])).

cnf(c_275,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_295,c_282,c_275,c_8])).


%------------------------------------------------------------------------------
