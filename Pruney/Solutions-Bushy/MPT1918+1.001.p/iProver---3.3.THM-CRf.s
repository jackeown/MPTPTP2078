%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1918+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:53 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 158 expanded)
%              Number of clauses        :   26 (  43 expanded)
%              Number of leaves         :    7 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  165 ( 621 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_0(X2,X1)
               => m1_yellow_0(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,X0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_yellow_0(X2,X0)
          & m1_yellow_0(X2,X1) )
     => ( ~ m1_yellow_0(sK2,X0)
        & m1_yellow_0(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,X0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_yellow_0(X2,X0)
            & m1_yellow_0(X2,sK1) )
        & m1_yellow_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow_0(X2,X0)
                & m1_yellow_0(X2,X1) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,sK0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    & m1_yellow_0(sK2,sK1)
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15,f14,f13])).

fof(f23,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ~ m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_237,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | ~ r1_tarski(X2_36,X0_36)
    | r1_tarski(X2_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_272,plain,
    ( ~ r1_tarski(X0_36,u1_orders_2(sK1))
    | r1_tarski(X0_36,u1_orders_2(sK0))
    | ~ r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_303,plain,
    ( ~ r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0)) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ r1_tarski(X0_36,u1_struct_0(sK1))
    | r1_tarski(X0_36,u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_291,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_3,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_161,plain,
    ( l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_2,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_49,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_3])).

cnf(c_50,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_49])).

cnf(c_151,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[status(thm)],[c_50,c_7])).

cnf(c_1,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_54,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_3])).

cnf(c_55,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_54])).

cnf(c_141,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[status(thm)],[c_55,c_7])).

cnf(c_6,negated_conjecture,
    ( m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_132,plain,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_3,c_6])).

cnf(c_123,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_50,c_6])).

cnf(c_114,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_55,c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,negated_conjecture,
    ( ~ m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_98,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_0,c_5])).

cnf(c_8,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_303,c_291,c_161,c_151,c_141,c_132,c_123,c_114,c_98,c_8])).


%------------------------------------------------------------------------------
