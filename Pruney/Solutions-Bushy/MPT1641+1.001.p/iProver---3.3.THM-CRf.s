%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1641+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:04 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 226 expanded)
%              Number of clauses        :   41 (  51 expanded)
%              Number of leaves         :   10 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  319 (1280 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                 => r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,sK3))
        & r1_orders_2(X0,X1,sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_tarski(k5_waybel_0(X0,sK2),k5_waybel_0(X0,X2))
            & r1_orders_2(X0,sK2,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(sK1,X1),k5_waybel_0(sK1,X2))
              & r1_orders_2(sK1,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3))
    & r1_orders_2(sK1,sK2,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f25,f24,f23])).

fof(f35,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ~ r1_tarski(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    r1_orders_2(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_156,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X1,X2)
    | r1_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_5,c_12])).

cnf(c_11,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,X1,X2)
    | ~ r1_orders_2(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_156,c_11])).

cnf(c_159,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X1,X2)
    | r1_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_158])).

cnf(c_400,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X1_43,X2_43)
    | r1_orders_2(sK1,X0_43,X2_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_159])).

cnf(c_464,plain,
    ( r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),X0_43)
    | ~ r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),sK2)
    | ~ r1_orders_2(sK1,sK2,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_468,plain,
    ( r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),sK3)
    | ~ r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),sK2)
    | ~ r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_140,plain,
    ( r2_hidden(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),k5_waybel_0(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_1,c_7])).

cnf(c_265,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(X0))
    | m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),X0) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

cnf(c_398,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(X0_44))
    | m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),X0_44) ),
    inference(subtyping,[status(esa)],[c_265])).

cnf(c_451,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k5_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_2,c_11])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_238,plain,
    ( m1_subset_1(k5_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_234,c_13])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k5_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | m1_subset_1(k5_waybel_0(sK1,X0_43),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_409,plain,
    ( m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_146,plain,
    ( ~ r2_hidden(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),k5_waybel_0(sK1,sK3)) ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_211,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X0,k5_waybel_0(sK1,X1))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_3,c_11])).

cnf(c_215,plain,
    ( r2_hidden(X0,k5_waybel_0(sK1,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_211,c_13])).

cnf(c_216,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X0,k5_waybel_0(sK1,X1)) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_309,plain,
    ( ~ r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_146,c_216])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_188,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X0,k5_waybel_0(sK1,X1))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_4,c_11])).

cnf(c_192,plain,
    ( ~ r2_hidden(X0,k5_waybel_0(sK1,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r1_orders_2(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_188,c_13])).

cnf(c_193,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X0,k5_waybel_0(sK1,X1)) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_296,plain,
    ( r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),sK2)
    | ~ m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_140,c_193])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_298,plain,
    ( ~ m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),u1_struct_0(sK1))
    | r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_10])).

cnf(c_299,plain,
    ( r1_orders_2(sK1,sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),sK2)
    | ~ m1_subset_1(sK0(k5_waybel_0(sK1,sK2),k5_waybel_0(sK1,sK3)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_298])).

cnf(c_8,negated_conjecture,
    ( r1_orders_2(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_468,c_451,c_409,c_309,c_299,c_8,c_9,c_10])).


%------------------------------------------------------------------------------
