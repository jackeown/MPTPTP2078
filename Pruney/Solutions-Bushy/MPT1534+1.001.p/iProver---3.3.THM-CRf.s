%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1534+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:48 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 192 expanded)
%              Number of clauses        :   33 (  40 expanded)
%              Number of leaves         :    7 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 (1281 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X2) )
               => r1_lattice3(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X2) )
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X3,X2)
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X3,X2)
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattice3(X0,X1,X3)
          & r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattice3(X0,X1,sK4)
        & r1_orders_2(X0,sK4,X2)
        & r1_lattice3(X0,X1,X2)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X3,X2)
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_lattice3(X0,sK2,X3)
            & r1_orders_2(X0,X3,sK3)
            & r1_lattice3(X0,sK2,sK3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ~ r1_lattice3(X0,X1,X3)
                & r1_orders_2(X0,X3,X2)
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ~ r1_lattice3(sK1,X1,X3)
              & r1_orders_2(sK1,X3,X2)
              & r1_lattice3(sK1,X1,X2)
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v4_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    & r1_orders_2(sK1,sK4,sK3)
    & r1_lattice3(sK1,sK2,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v4_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f17,f16,f15])).

fof(f24,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ~ r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    r1_orders_2(sK1,sK4,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    r1_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_116,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X0)
    | r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_4,c_11])).

cnf(c_10,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_118,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X2,X0)
    | ~ r1_orders_2(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_116,c_10])).

cnf(c_119,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X0)
    | r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_118])).

cnf(c_347,plain,
    ( ~ r1_orders_2(sK1,X0_41,X1_41)
    | ~ r1_orders_2(sK1,X2_41,X0_41)
    | r1_orders_2(sK1,X2_41,X1_41)
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_119])).

cnf(c_405,plain,
    ( ~ r1_orders_2(sK1,X0_41,X1_41)
    | ~ r1_orders_2(sK1,X1_41,sK0(sK1,sK2,sK4))
    | r1_orders_2(sK1,X0_41,sK0(sK1,sK2,sK4))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,sK4),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_410,plain,
    ( ~ r1_orders_2(sK1,X0_41,sK0(sK1,sK2,sK4))
    | ~ r1_orders_2(sK1,sK4,X0_41)
    | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK4))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_412,plain,
    ( ~ r1_orders_2(sK1,sK3,sK0(sK1,sK2,sK4))
    | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK4))
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK0(sK1,sK2,sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_183,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r1_lattice3(sK1,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_217,plain,
    ( r1_lattice3(sK1,X0,X1)
    | r2_hidden(sK0(sK1,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_263,plain,
    ( r1_orders_2(sK1,X0,sK0(sK1,X1,X2))
    | ~ r1_lattice3(sK1,X1,X0)
    | r1_lattice3(sK1,X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,X1,X2),u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_183,c_217])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_203,plain,
    ( r1_lattice3(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_277,plain,
    ( r1_orders_2(sK1,X0,sK0(sK1,X1,X2))
    | ~ r1_lattice3(sK1,X1,X0)
    | r1_lattice3(sK1,X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_263,c_203])).

cnf(c_344,plain,
    ( r1_orders_2(sK1,X0_41,sK0(sK1,X0_42,X1_41))
    | ~ r1_lattice3(sK1,X0_42,X0_41)
    | r1_lattice3(sK1,X0_42,X1_41)
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_400,plain,
    ( r1_orders_2(sK1,X0_41,sK0(sK1,sK2,sK4))
    | ~ r1_lattice3(sK1,sK2,X0_41)
    | r1_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_402,plain,
    ( r1_orders_2(sK1,sK3,sK0(sK1,sK2,sK4))
    | ~ r1_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_231,plain,
    ( ~ r1_orders_2(sK1,X0,sK0(sK1,X1,X0))
    | r1_lattice3(sK1,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_0,c_10])).

cnf(c_345,plain,
    ( ~ r1_orders_2(sK1,X0_41,sK0(sK1,X0_42,X0_41))
    | r1_lattice3(sK1,X0_42,X0_41)
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_231])).

cnf(c_392,plain,
    ( ~ r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK4))
    | r1_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_346,plain,
    ( r1_lattice3(sK1,X0_42,X0_41)
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_42,X0_41),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_389,plain,
    ( r1_lattice3(sK1,sK2,sK4)
    | m1_subset_1(sK0(sK1,sK2,sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_5,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,negated_conjecture,
    ( r1_orders_2(sK1,sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,negated_conjecture,
    ( r1_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_412,c_402,c_392,c_389,c_5,c_6,c_7,c_8,c_9])).


%------------------------------------------------------------------------------
