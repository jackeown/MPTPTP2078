%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:26 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 109 expanded)
%              Number of clauses        :   41 (  47 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  271 ( 393 expanded)
%              Number of equality atoms :   34 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r1_lattice3(X0,k1_xboole_0,X1)
              & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,k1_xboole_0,sK4)
          | ~ r2_lattice3(X0,k1_xboole_0,sK4) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
              | ~ r2_lattice3(X0,k1_xboole_0,X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_lattice3(sK3,k1_xboole_0,X1)
            | ~ r2_lattice3(sK3,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ r1_lattice3(sK3,k1_xboole_0,sK4)
      | ~ r2_lattice3(sK3,k1_xboole_0,sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f26,f25])).

fof(f40,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f42,plain,
    ( ~ r1_lattice3(sK3,k1_xboole_0,sK4)
    | ~ r2_lattice3(sK3,k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1148,plain,
    ( ~ r2_lattice3(X0_43,X0_45,X0_44)
    | r2_lattice3(X0_43,X1_45,X1_44)
    | X1_45 != X0_45
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1758,plain,
    ( r2_lattice3(sK3,X0_45,X0_44)
    | ~ r2_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X1_44)
    | X0_45 != k3_xboole_0(X0_47,k1_xboole_0)
    | X0_44 != X1_44 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1760,plain,
    ( ~ r2_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
    | r2_lattice3(sK3,k1_xboole_0,sK4)
    | k1_xboole_0 != k3_xboole_0(iProver_bot,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_175,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_176,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_1134,plain,
    ( ~ r2_hidden(X0_44,k3_xboole_0(X0_47,k1_xboole_0)) ),
    inference(subtyping,[status(esa)],[c_176])).

cnf(c_1688,plain,
    ( ~ r2_hidden(sK2(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1694,plain,
    ( ~ r2_hidden(sK2(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_225,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_226,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_1131,plain,
    ( r2_lattice3(sK3,X0_45,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,X0_45,X0_44),X0_45) ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_1687,plain,
    ( r2_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_1690,plain,
    ( r2_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_1142,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1654,plain,
    ( X0_45 != X1_45
    | X0_45 = k3_xboole_0(X0_47,k1_xboole_0)
    | k3_xboole_0(X0_47,k1_xboole_0) != X1_45 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_1655,plain,
    ( k3_xboole_0(iProver_bot,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(iProver_bot,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_1145,plain,
    ( ~ r1_lattice3(X0_43,X0_45,X0_44)
    | r1_lattice3(X0_43,X1_45,X1_44)
    | X1_45 != X0_45
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1584,plain,
    ( r1_lattice3(sK3,X0_45,X0_44)
    | ~ r1_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X1_44)
    | X0_45 != k3_xboole_0(X0_47,k1_xboole_0)
    | X0_44 != X1_44 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_1586,plain,
    ( ~ r1_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
    | r1_lattice3(sK3,k1_xboole_0,sK4)
    | k1_xboole_0 != k3_xboole_0(iProver_bot,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_291,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_292,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_1127,plain,
    ( r1_lattice3(sK3,X0_45,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0_45,X0_44),X0_45) ),
    inference(subtyping,[status(esa)],[c_292])).

cnf(c_1546,plain,
    ( r1_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1552,plain,
    ( r1_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_1545,plain,
    ( ~ r2_hidden(sK1(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1548,plain,
    ( ~ r2_hidden(sK1(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1138,plain,
    ( k3_xboole_0(X0_47,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1158,plain,
    ( k3_xboole_0(iProver_bot,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_1141,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1157,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_1140,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1156,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_12,negated_conjecture,
    ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
    | ~ r1_lattice3(sK3,k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1760,c_1694,c_1690,c_1655,c_1586,c_1552,c_1548,c_1158,c_1157,c_1156,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.95/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.95/0.98  
% 0.95/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.95/0.98  
% 0.95/0.98  ------  iProver source info
% 0.95/0.98  
% 0.95/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.95/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.95/0.98  git: non_committed_changes: false
% 0.95/0.98  git: last_make_outside_of_git: false
% 0.95/0.98  
% 0.95/0.98  ------ 
% 0.95/0.98  
% 0.95/0.98  ------ Input Options
% 0.95/0.98  
% 0.95/0.98  --out_options                           all
% 0.95/0.98  --tptp_safe_out                         true
% 0.95/0.98  --problem_path                          ""
% 0.95/0.98  --include_path                          ""
% 0.95/0.98  --clausifier                            res/vclausify_rel
% 0.95/0.98  --clausifier_options                    --mode clausify
% 0.95/0.98  --stdin                                 false
% 0.95/0.98  --stats_out                             all
% 0.95/0.98  
% 0.95/0.98  ------ General Options
% 0.95/0.98  
% 0.95/0.98  --fof                                   false
% 0.95/0.98  --time_out_real                         305.
% 0.95/0.98  --time_out_virtual                      -1.
% 0.95/0.98  --symbol_type_check                     false
% 0.95/0.98  --clausify_out                          false
% 0.95/0.98  --sig_cnt_out                           false
% 0.95/0.98  --trig_cnt_out                          false
% 0.95/0.98  --trig_cnt_out_tolerance                1.
% 0.95/0.98  --trig_cnt_out_sk_spl                   false
% 0.95/0.98  --abstr_cl_out                          false
% 0.95/0.98  
% 0.95/0.98  ------ Global Options
% 0.95/0.98  
% 0.95/0.98  --schedule                              default
% 0.95/0.98  --add_important_lit                     false
% 0.95/0.98  --prop_solver_per_cl                    1000
% 0.95/0.98  --min_unsat_core                        false
% 0.95/0.98  --soft_assumptions                      false
% 0.95/0.98  --soft_lemma_size                       3
% 0.95/0.98  --prop_impl_unit_size                   0
% 0.95/0.98  --prop_impl_unit                        []
% 0.95/0.98  --share_sel_clauses                     true
% 0.95/0.98  --reset_solvers                         false
% 0.95/0.98  --bc_imp_inh                            [conj_cone]
% 0.95/0.98  --conj_cone_tolerance                   3.
% 0.95/0.98  --extra_neg_conj                        none
% 0.95/0.98  --large_theory_mode                     true
% 0.95/0.98  --prolific_symb_bound                   200
% 0.95/0.98  --lt_threshold                          2000
% 0.95/0.98  --clause_weak_htbl                      true
% 0.95/0.98  --gc_record_bc_elim                     false
% 0.95/0.98  
% 0.95/0.98  ------ Preprocessing Options
% 0.95/0.98  
% 0.95/0.98  --preprocessing_flag                    true
% 0.95/0.98  --time_out_prep_mult                    0.1
% 0.95/0.98  --splitting_mode                        input
% 0.95/0.98  --splitting_grd                         true
% 0.95/0.98  --splitting_cvd                         false
% 0.95/0.98  --splitting_cvd_svl                     false
% 0.95/0.98  --splitting_nvd                         32
% 0.95/0.98  --sub_typing                            true
% 0.95/0.98  --prep_gs_sim                           true
% 0.95/0.98  --prep_unflatten                        true
% 0.95/0.98  --prep_res_sim                          true
% 0.95/0.98  --prep_upred                            true
% 0.95/0.98  --prep_sem_filter                       exhaustive
% 0.95/0.98  --prep_sem_filter_out                   false
% 0.95/0.98  --pred_elim                             true
% 0.95/0.98  --res_sim_input                         true
% 0.95/0.98  --eq_ax_congr_red                       true
% 0.95/0.98  --pure_diseq_elim                       true
% 0.95/0.98  --brand_transform                       false
% 0.95/0.98  --non_eq_to_eq                          false
% 0.95/0.98  --prep_def_merge                        true
% 0.95/0.98  --prep_def_merge_prop_impl              false
% 0.95/0.98  --prep_def_merge_mbd                    true
% 0.95/0.98  --prep_def_merge_tr_red                 false
% 0.95/0.98  --prep_def_merge_tr_cl                  false
% 0.95/0.98  --smt_preprocessing                     true
% 0.95/0.98  --smt_ac_axioms                         fast
% 0.95/0.98  --preprocessed_out                      false
% 0.95/0.98  --preprocessed_stats                    false
% 0.95/0.98  
% 0.95/0.98  ------ Abstraction refinement Options
% 0.95/0.98  
% 0.95/0.98  --abstr_ref                             []
% 0.95/0.98  --abstr_ref_prep                        false
% 0.95/0.98  --abstr_ref_until_sat                   false
% 0.95/0.98  --abstr_ref_sig_restrict                funpre
% 0.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.98  --abstr_ref_under                       []
% 0.95/0.98  
% 0.95/0.98  ------ SAT Options
% 0.95/0.98  
% 0.95/0.98  --sat_mode                              false
% 0.95/0.98  --sat_fm_restart_options                ""
% 0.95/0.98  --sat_gr_def                            false
% 0.95/0.98  --sat_epr_types                         true
% 0.95/0.98  --sat_non_cyclic_types                  false
% 0.95/0.98  --sat_finite_models                     false
% 0.95/0.98  --sat_fm_lemmas                         false
% 0.95/0.98  --sat_fm_prep                           false
% 0.95/0.98  --sat_fm_uc_incr                        true
% 0.95/0.98  --sat_out_model                         small
% 0.95/0.98  --sat_out_clauses                       false
% 0.95/0.98  
% 0.95/0.98  ------ QBF Options
% 0.95/0.98  
% 0.95/0.98  --qbf_mode                              false
% 0.95/0.98  --qbf_elim_univ                         false
% 0.95/0.98  --qbf_dom_inst                          none
% 0.95/0.98  --qbf_dom_pre_inst                      false
% 0.95/0.98  --qbf_sk_in                             false
% 0.95/0.98  --qbf_pred_elim                         true
% 0.95/0.98  --qbf_split                             512
% 0.95/0.98  
% 0.95/0.98  ------ BMC1 Options
% 0.95/0.98  
% 0.95/0.98  --bmc1_incremental                      false
% 0.95/0.98  --bmc1_axioms                           reachable_all
% 0.95/0.98  --bmc1_min_bound                        0
% 0.95/0.98  --bmc1_max_bound                        -1
% 0.95/0.98  --bmc1_max_bound_default                -1
% 0.95/0.98  --bmc1_symbol_reachability              true
% 0.95/0.98  --bmc1_property_lemmas                  false
% 0.95/0.98  --bmc1_k_induction                      false
% 0.95/0.98  --bmc1_non_equiv_states                 false
% 0.95/0.98  --bmc1_deadlock                         false
% 0.95/0.98  --bmc1_ucm                              false
% 0.95/0.98  --bmc1_add_unsat_core                   none
% 0.95/0.98  --bmc1_unsat_core_children              false
% 0.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.98  --bmc1_out_stat                         full
% 0.95/0.98  --bmc1_ground_init                      false
% 0.95/0.98  --bmc1_pre_inst_next_state              false
% 0.95/0.98  --bmc1_pre_inst_state                   false
% 0.95/0.98  --bmc1_pre_inst_reach_state             false
% 0.95/0.98  --bmc1_out_unsat_core                   false
% 0.95/0.98  --bmc1_aig_witness_out                  false
% 0.95/0.98  --bmc1_verbose                          false
% 0.95/0.98  --bmc1_dump_clauses_tptp                false
% 0.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.98  --bmc1_dump_file                        -
% 0.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.98  --bmc1_ucm_extend_mode                  1
% 0.95/0.98  --bmc1_ucm_init_mode                    2
% 0.95/0.98  --bmc1_ucm_cone_mode                    none
% 0.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.98  --bmc1_ucm_relax_model                  4
% 0.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.98  --bmc1_ucm_layered_model                none
% 0.95/0.98  --bmc1_ucm_max_lemma_size               10
% 0.95/0.98  
% 0.95/0.98  ------ AIG Options
% 0.95/0.98  
% 0.95/0.98  --aig_mode                              false
% 0.95/0.98  
% 0.95/0.98  ------ Instantiation Options
% 0.95/0.98  
% 0.95/0.98  --instantiation_flag                    true
% 0.95/0.98  --inst_sos_flag                         false
% 0.95/0.98  --inst_sos_phase                        true
% 0.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.98  --inst_lit_sel_side                     num_symb
% 0.95/0.98  --inst_solver_per_active                1400
% 0.95/0.98  --inst_solver_calls_frac                1.
% 0.95/0.98  --inst_passive_queue_type               priority_queues
% 0.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.98  --inst_passive_queues_freq              [25;2]
% 0.95/0.98  --inst_dismatching                      true
% 0.95/0.98  --inst_eager_unprocessed_to_passive     true
% 0.95/0.98  --inst_prop_sim_given                   true
% 0.95/0.98  --inst_prop_sim_new                     false
% 0.95/0.98  --inst_subs_new                         false
% 0.95/0.98  --inst_eq_res_simp                      false
% 0.95/0.98  --inst_subs_given                       false
% 0.95/0.98  --inst_orphan_elimination               true
% 0.95/0.98  --inst_learning_loop_flag               true
% 0.95/0.98  --inst_learning_start                   3000
% 0.95/0.98  --inst_learning_factor                  2
% 0.95/0.98  --inst_start_prop_sim_after_learn       3
% 0.95/0.98  --inst_sel_renew                        solver
% 0.95/0.98  --inst_lit_activity_flag                true
% 0.95/0.98  --inst_restr_to_given                   false
% 0.95/0.98  --inst_activity_threshold               500
% 0.95/0.98  --inst_out_proof                        true
% 0.95/0.98  
% 0.95/0.98  ------ Resolution Options
% 0.95/0.98  
% 0.95/0.98  --resolution_flag                       true
% 0.95/0.98  --res_lit_sel                           adaptive
% 0.95/0.98  --res_lit_sel_side                      none
% 0.95/0.98  --res_ordering                          kbo
% 0.95/0.98  --res_to_prop_solver                    active
% 0.95/0.98  --res_prop_simpl_new                    false
% 0.95/0.98  --res_prop_simpl_given                  true
% 0.95/0.98  --res_passive_queue_type                priority_queues
% 0.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/0.98  --res_passive_queues_freq               [15;5]
% 0.95/0.98  --res_forward_subs                      full
% 0.95/0.98  --res_backward_subs                     full
% 0.95/0.98  --res_forward_subs_resolution           true
% 0.95/0.98  --res_backward_subs_resolution          true
% 0.95/0.98  --res_orphan_elimination                true
% 0.95/0.98  --res_time_limit                        2.
% 0.95/0.98  --res_out_proof                         true
% 0.95/0.98  
% 0.95/0.98  ------ Superposition Options
% 0.95/0.98  
% 0.95/0.98  --superposition_flag                    true
% 0.95/0.98  --sup_passive_queue_type                priority_queues
% 0.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.95/0.98  --demod_completeness_check              fast
% 0.95/0.98  --demod_use_ground                      true
% 0.95/0.98  --sup_to_prop_solver                    passive
% 0.95/0.98  --sup_prop_simpl_new                    true
% 0.95/0.98  --sup_prop_simpl_given                  true
% 0.95/0.98  --sup_fun_splitting                     false
% 0.95/0.98  --sup_smt_interval                      50000
% 0.95/0.98  
% 0.95/0.98  ------ Superposition Simplification Setup
% 0.95/0.98  
% 0.95/0.98  --sup_indices_passive                   []
% 0.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.98  --sup_full_bw                           [BwDemod]
% 0.95/0.98  --sup_immed_triv                        [TrivRules]
% 0.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.98  --sup_immed_bw_main                     []
% 0.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.98  
% 0.95/0.98  ------ Combination Options
% 0.95/0.98  
% 0.95/0.98  --comb_res_mult                         3
% 0.95/0.98  --comb_sup_mult                         2
% 0.95/0.98  --comb_inst_mult                        10
% 0.95/0.98  
% 0.95/0.98  ------ Debug Options
% 0.95/0.98  
% 0.95/0.98  --dbg_backtrace                         false
% 0.95/0.98  --dbg_dump_prop_clauses                 false
% 0.95/0.98  --dbg_dump_prop_clauses_file            -
% 0.95/0.98  --dbg_out_stat                          false
% 0.95/0.98  ------ Parsing...
% 0.95/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.95/0.98  
% 0.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.95/0.98  
% 0.95/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.95/0.98  
% 0.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.95/0.98  ------ Proving...
% 0.95/0.98  ------ Problem Properties 
% 0.95/0.98  
% 0.95/0.98  
% 0.95/0.98  clauses                                 13
% 0.95/0.98  conjectures                             2
% 0.95/0.98  EPR                                     1
% 0.95/0.98  Horn                                    9
% 0.95/0.98  unary                                   3
% 0.95/0.98  binary                                  2
% 0.95/0.98  lits                                    35
% 0.95/0.98  lits eq                                 1
% 0.95/0.98  fd_pure                                 0
% 0.95/0.98  fd_pseudo                               0
% 0.95/0.98  fd_cond                                 0
% 0.95/0.98  fd_pseudo_cond                          0
% 0.95/0.98  AC symbols                              0
% 0.95/0.98  
% 0.95/0.98  ------ Schedule dynamic 5 is on 
% 0.95/0.98  
% 0.95/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.95/0.98  
% 0.95/0.98  
% 0.95/0.98  ------ 
% 0.95/0.98  Current options:
% 0.95/0.98  ------ 
% 0.95/0.98  
% 0.95/0.98  ------ Input Options
% 0.95/0.98  
% 0.95/0.98  --out_options                           all
% 0.95/0.98  --tptp_safe_out                         true
% 0.95/0.98  --problem_path                          ""
% 0.95/0.98  --include_path                          ""
% 0.95/0.98  --clausifier                            res/vclausify_rel
% 0.95/0.98  --clausifier_options                    --mode clausify
% 0.95/0.98  --stdin                                 false
% 0.95/0.98  --stats_out                             all
% 0.95/0.98  
% 0.95/0.98  ------ General Options
% 0.95/0.98  
% 0.95/0.98  --fof                                   false
% 0.95/0.98  --time_out_real                         305.
% 0.95/0.98  --time_out_virtual                      -1.
% 0.95/0.98  --symbol_type_check                     false
% 0.95/0.98  --clausify_out                          false
% 0.95/0.98  --sig_cnt_out                           false
% 0.95/0.98  --trig_cnt_out                          false
% 0.95/0.98  --trig_cnt_out_tolerance                1.
% 0.95/0.98  --trig_cnt_out_sk_spl                   false
% 0.95/0.98  --abstr_cl_out                          false
% 0.95/0.98  
% 0.95/0.98  ------ Global Options
% 0.95/0.98  
% 0.95/0.98  --schedule                              default
% 0.95/0.98  --add_important_lit                     false
% 0.95/0.98  --prop_solver_per_cl                    1000
% 0.95/0.98  --min_unsat_core                        false
% 0.95/0.98  --soft_assumptions                      false
% 0.95/0.98  --soft_lemma_size                       3
% 0.95/0.98  --prop_impl_unit_size                   0
% 0.95/0.98  --prop_impl_unit                        []
% 0.95/0.98  --share_sel_clauses                     true
% 0.95/0.98  --reset_solvers                         false
% 0.95/0.98  --bc_imp_inh                            [conj_cone]
% 0.95/0.98  --conj_cone_tolerance                   3.
% 0.95/0.98  --extra_neg_conj                        none
% 0.95/0.98  --large_theory_mode                     true
% 0.95/0.98  --prolific_symb_bound                   200
% 0.95/0.98  --lt_threshold                          2000
% 0.95/0.98  --clause_weak_htbl                      true
% 0.95/0.98  --gc_record_bc_elim                     false
% 0.95/0.98  
% 0.95/0.98  ------ Preprocessing Options
% 0.95/0.98  
% 0.95/0.98  --preprocessing_flag                    true
% 0.95/0.98  --time_out_prep_mult                    0.1
% 0.95/0.98  --splitting_mode                        input
% 0.95/0.98  --splitting_grd                         true
% 0.95/0.98  --splitting_cvd                         false
% 0.95/0.98  --splitting_cvd_svl                     false
% 0.95/0.98  --splitting_nvd                         32
% 0.95/0.98  --sub_typing                            true
% 0.95/0.98  --prep_gs_sim                           true
% 0.95/0.98  --prep_unflatten                        true
% 0.95/0.98  --prep_res_sim                          true
% 0.95/0.98  --prep_upred                            true
% 0.95/0.98  --prep_sem_filter                       exhaustive
% 0.95/0.98  --prep_sem_filter_out                   false
% 0.95/0.98  --pred_elim                             true
% 0.95/0.98  --res_sim_input                         true
% 0.95/0.98  --eq_ax_congr_red                       true
% 0.95/0.98  --pure_diseq_elim                       true
% 0.95/0.98  --brand_transform                       false
% 0.95/0.98  --non_eq_to_eq                          false
% 0.95/0.98  --prep_def_merge                        true
% 0.95/0.98  --prep_def_merge_prop_impl              false
% 0.95/0.98  --prep_def_merge_mbd                    true
% 0.95/0.98  --prep_def_merge_tr_red                 false
% 0.95/0.98  --prep_def_merge_tr_cl                  false
% 0.95/0.98  --smt_preprocessing                     true
% 0.95/0.98  --smt_ac_axioms                         fast
% 0.95/0.98  --preprocessed_out                      false
% 0.95/0.98  --preprocessed_stats                    false
% 0.95/0.98  
% 0.95/0.98  ------ Abstraction refinement Options
% 0.95/0.98  
% 0.95/0.98  --abstr_ref                             []
% 0.95/0.98  --abstr_ref_prep                        false
% 0.95/0.98  --abstr_ref_until_sat                   false
% 0.95/0.98  --abstr_ref_sig_restrict                funpre
% 0.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.98  --abstr_ref_under                       []
% 0.95/0.98  
% 0.95/0.98  ------ SAT Options
% 0.95/0.98  
% 0.95/0.98  --sat_mode                              false
% 0.95/0.98  --sat_fm_restart_options                ""
% 0.95/0.98  --sat_gr_def                            false
% 0.95/0.98  --sat_epr_types                         true
% 0.95/0.98  --sat_non_cyclic_types                  false
% 0.95/0.98  --sat_finite_models                     false
% 0.95/0.98  --sat_fm_lemmas                         false
% 0.95/0.98  --sat_fm_prep                           false
% 0.95/0.98  --sat_fm_uc_incr                        true
% 0.95/0.98  --sat_out_model                         small
% 0.95/0.98  --sat_out_clauses                       false
% 0.95/0.98  
% 0.95/0.98  ------ QBF Options
% 0.95/0.98  
% 0.95/0.98  --qbf_mode                              false
% 0.95/0.98  --qbf_elim_univ                         false
% 0.95/0.98  --qbf_dom_inst                          none
% 0.95/0.98  --qbf_dom_pre_inst                      false
% 0.95/0.98  --qbf_sk_in                             false
% 0.95/0.98  --qbf_pred_elim                         true
% 0.95/0.98  --qbf_split                             512
% 0.95/0.98  
% 0.95/0.98  ------ BMC1 Options
% 0.95/0.98  
% 0.95/0.98  --bmc1_incremental                      false
% 0.95/0.98  --bmc1_axioms                           reachable_all
% 0.95/0.98  --bmc1_min_bound                        0
% 0.95/0.98  --bmc1_max_bound                        -1
% 0.95/0.98  --bmc1_max_bound_default                -1
% 0.95/0.98  --bmc1_symbol_reachability              true
% 0.95/0.98  --bmc1_property_lemmas                  false
% 0.95/0.98  --bmc1_k_induction                      false
% 0.95/0.98  --bmc1_non_equiv_states                 false
% 0.95/0.98  --bmc1_deadlock                         false
% 0.95/0.98  --bmc1_ucm                              false
% 0.95/0.98  --bmc1_add_unsat_core                   none
% 0.95/0.98  --bmc1_unsat_core_children              false
% 0.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.98  --bmc1_out_stat                         full
% 0.95/0.98  --bmc1_ground_init                      false
% 0.95/0.98  --bmc1_pre_inst_next_state              false
% 0.95/0.98  --bmc1_pre_inst_state                   false
% 0.95/0.98  --bmc1_pre_inst_reach_state             false
% 0.95/0.98  --bmc1_out_unsat_core                   false
% 0.95/0.98  --bmc1_aig_witness_out                  false
% 0.95/0.98  --bmc1_verbose                          false
% 0.95/0.98  --bmc1_dump_clauses_tptp                false
% 0.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.98  --bmc1_dump_file                        -
% 0.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.98  --bmc1_ucm_extend_mode                  1
% 0.95/0.98  --bmc1_ucm_init_mode                    2
% 0.95/0.98  --bmc1_ucm_cone_mode                    none
% 0.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.98  --bmc1_ucm_relax_model                  4
% 0.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.98  --bmc1_ucm_layered_model                none
% 0.95/0.98  --bmc1_ucm_max_lemma_size               10
% 0.95/0.98  
% 0.95/0.98  ------ AIG Options
% 0.95/0.98  
% 0.95/0.98  --aig_mode                              false
% 0.95/0.98  
% 0.95/0.98  ------ Instantiation Options
% 0.95/0.98  
% 0.95/0.98  --instantiation_flag                    true
% 0.95/0.98  --inst_sos_flag                         false
% 0.95/0.98  --inst_sos_phase                        true
% 0.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.98  --inst_lit_sel_side                     none
% 0.95/0.98  --inst_solver_per_active                1400
% 0.95/0.98  --inst_solver_calls_frac                1.
% 0.95/0.98  --inst_passive_queue_type               priority_queues
% 0.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.98  --inst_passive_queues_freq              [25;2]
% 0.95/0.98  --inst_dismatching                      true
% 0.95/0.98  --inst_eager_unprocessed_to_passive     true
% 0.95/0.98  --inst_prop_sim_given                   true
% 0.95/0.98  --inst_prop_sim_new                     false
% 0.95/0.98  --inst_subs_new                         false
% 0.95/0.98  --inst_eq_res_simp                      false
% 0.95/0.98  --inst_subs_given                       false
% 0.95/0.98  --inst_orphan_elimination               true
% 0.95/0.98  --inst_learning_loop_flag               true
% 0.95/0.98  --inst_learning_start                   3000
% 0.95/0.98  --inst_learning_factor                  2
% 0.95/0.98  --inst_start_prop_sim_after_learn       3
% 0.95/0.98  --inst_sel_renew                        solver
% 0.95/0.98  --inst_lit_activity_flag                true
% 0.95/0.98  --inst_restr_to_given                   false
% 0.95/0.98  --inst_activity_threshold               500
% 0.95/0.98  --inst_out_proof                        true
% 0.95/0.98  
% 0.95/0.98  ------ Resolution Options
% 0.95/0.98  
% 0.95/0.98  --resolution_flag                       false
% 0.95/0.98  --res_lit_sel                           adaptive
% 0.95/0.98  --res_lit_sel_side                      none
% 0.95/0.98  --res_ordering                          kbo
% 0.95/0.98  --res_to_prop_solver                    active
% 0.95/0.98  --res_prop_simpl_new                    false
% 0.95/0.98  --res_prop_simpl_given                  true
% 0.95/0.98  --res_passive_queue_type                priority_queues
% 0.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/0.98  --res_passive_queues_freq               [15;5]
% 0.95/0.98  --res_forward_subs                      full
% 0.95/0.98  --res_backward_subs                     full
% 0.95/0.98  --res_forward_subs_resolution           true
% 0.95/0.98  --res_backward_subs_resolution          true
% 0.95/0.98  --res_orphan_elimination                true
% 0.95/0.98  --res_time_limit                        2.
% 0.95/0.98  --res_out_proof                         true
% 0.95/0.98  
% 0.95/0.98  ------ Superposition Options
% 0.95/0.98  
% 0.95/0.98  --superposition_flag                    true
% 0.95/0.98  --sup_passive_queue_type                priority_queues
% 0.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.95/0.98  --demod_completeness_check              fast
% 0.95/0.98  --demod_use_ground                      true
% 0.95/0.98  --sup_to_prop_solver                    passive
% 0.95/0.98  --sup_prop_simpl_new                    true
% 0.95/0.98  --sup_prop_simpl_given                  true
% 0.95/0.98  --sup_fun_splitting                     false
% 0.95/0.98  --sup_smt_interval                      50000
% 0.95/0.98  
% 0.95/0.98  ------ Superposition Simplification Setup
% 0.95/0.98  
% 0.95/0.98  --sup_indices_passive                   []
% 0.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.98  --sup_full_bw                           [BwDemod]
% 0.95/0.98  --sup_immed_triv                        [TrivRules]
% 0.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.98  --sup_immed_bw_main                     []
% 0.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.98  
% 0.95/0.98  ------ Combination Options
% 0.95/0.98  
% 0.95/0.98  --comb_res_mult                         3
% 0.95/0.98  --comb_sup_mult                         2
% 0.95/0.98  --comb_inst_mult                        10
% 0.95/0.98  
% 0.95/0.98  ------ Debug Options
% 0.95/0.98  
% 0.95/0.98  --dbg_backtrace                         false
% 0.95/0.98  --dbg_dump_prop_clauses                 false
% 0.95/0.98  --dbg_dump_prop_clauses_file            -
% 0.95/0.98  --dbg_out_stat                          false
% 0.95/0.98  
% 0.95/0.98  
% 0.95/0.98  
% 0.95/0.98  
% 0.95/0.98  ------ Proving...
% 0.95/0.98  
% 0.95/0.98  
% 0.95/0.98  % SZS status Theorem for theBenchmark.p
% 0.95/0.98  
% 0.95/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.95/0.98  
% 0.95/0.98  fof(f1,axiom,(
% 0.95/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.98  
% 0.95/0.98  fof(f8,plain,(
% 0.95/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.95/0.98    inference(rectify,[],[f1])).
% 0.95/0.98  
% 0.95/0.98  fof(f9,plain,(
% 0.95/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.95/0.98    inference(ennf_transformation,[],[f8])).
% 0.95/0.98  
% 0.95/0.98  fof(f15,plain,(
% 0.95/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 0.95/0.98    introduced(choice_axiom,[])).
% 0.95/0.98  
% 0.95/0.98  fof(f16,plain,(
% 0.95/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).
% 0.95/0.98  
% 0.95/0.98  fof(f29,plain,(
% 0.95/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.95/0.98    inference(cnf_transformation,[],[f16])).
% 0.95/0.98  
% 0.95/0.98  fof(f3,axiom,(
% 0.95/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.98  
% 0.95/0.98  fof(f31,plain,(
% 0.95/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.95/0.98    inference(cnf_transformation,[],[f3])).
% 0.95/0.98  
% 0.95/0.98  fof(f5,axiom,(
% 0.95/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.98  
% 0.95/0.98  fof(f12,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(ennf_transformation,[],[f5])).
% 0.95/0.98  
% 0.95/0.98  fof(f13,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(flattening,[],[f12])).
% 0.95/0.98  
% 0.95/0.98  fof(f21,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(nnf_transformation,[],[f13])).
% 0.95/0.98  
% 0.95/0.98  fof(f22,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(rectify,[],[f21])).
% 0.95/0.98  
% 0.95/0.98  fof(f23,plain,(
% 0.95/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.95/0.98    introduced(choice_axiom,[])).
% 0.95/0.98  
% 0.95/0.98  fof(f24,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.95/0.98  
% 0.95/0.98  fof(f38,plain,(
% 0.95/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.95/0.98    inference(cnf_transformation,[],[f24])).
% 0.95/0.98  
% 0.95/0.98  fof(f6,conjecture,(
% 0.95/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.98  
% 0.95/0.98  fof(f7,negated_conjecture,(
% 0.95/0.98    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.95/0.98    inference(negated_conjecture,[],[f6])).
% 0.95/0.98  
% 0.95/0.98  fof(f14,plain,(
% 0.95/0.98    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.95/0.98    inference(ennf_transformation,[],[f7])).
% 0.95/0.98  
% 0.95/0.98  fof(f26,plain,(
% 0.95/0.98    ( ! [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~r1_lattice3(X0,k1_xboole_0,sK4) | ~r2_lattice3(X0,k1_xboole_0,sK4)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 0.95/0.98    introduced(choice_axiom,[])).
% 0.95/0.98  
% 0.95/0.98  fof(f25,plain,(
% 0.95/0.98    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : ((~r1_lattice3(sK3,k1_xboole_0,X1) | ~r2_lattice3(sK3,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3))),
% 0.95/0.98    introduced(choice_axiom,[])).
% 0.95/0.98  
% 0.95/0.98  fof(f27,plain,(
% 0.95/0.98    ((~r1_lattice3(sK3,k1_xboole_0,sK4) | ~r2_lattice3(sK3,k1_xboole_0,sK4)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3)),
% 0.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f26,f25])).
% 0.95/0.98  
% 0.95/0.98  fof(f40,plain,(
% 0.95/0.98    l1_orders_2(sK3)),
% 0.95/0.98    inference(cnf_transformation,[],[f27])).
% 0.95/0.98  
% 0.95/0.98  fof(f4,axiom,(
% 0.95/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.98  
% 0.95/0.98  fof(f10,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(ennf_transformation,[],[f4])).
% 0.95/0.98  
% 0.95/0.98  fof(f11,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(flattening,[],[f10])).
% 0.95/0.98  
% 0.95/0.98  fof(f17,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(nnf_transformation,[],[f11])).
% 0.95/0.98  
% 0.95/0.98  fof(f18,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(rectify,[],[f17])).
% 0.95/0.98  
% 0.95/0.98  fof(f19,plain,(
% 0.95/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.95/0.98    introduced(choice_axiom,[])).
% 0.95/0.98  
% 0.95/0.98  fof(f20,plain,(
% 0.95/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 0.95/0.98  
% 0.95/0.98  fof(f34,plain,(
% 0.95/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.95/0.98    inference(cnf_transformation,[],[f20])).
% 0.95/0.98  
% 0.95/0.98  fof(f2,axiom,(
% 0.95/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 0.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.98  
% 0.95/0.98  fof(f30,plain,(
% 0.95/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 0.95/0.98    inference(cnf_transformation,[],[f2])).
% 0.95/0.98  
% 0.95/0.98  fof(f42,plain,(
% 0.95/0.98    ~r1_lattice3(sK3,k1_xboole_0,sK4) | ~r2_lattice3(sK3,k1_xboole_0,sK4)),
% 0.95/0.99    inference(cnf_transformation,[],[f27])).
% 0.95/0.99  
% 0.95/0.99  fof(f41,plain,(
% 0.95/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.95/0.99    inference(cnf_transformation,[],[f27])).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1148,plain,
% 0.95/0.99      ( ~ r2_lattice3(X0_43,X0_45,X0_44)
% 0.95/0.99      | r2_lattice3(X0_43,X1_45,X1_44)
% 0.95/0.99      | X1_45 != X0_45
% 0.95/0.99      | X1_44 != X0_44 ),
% 0.95/0.99      theory(equality) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1758,plain,
% 0.95/0.99      ( r2_lattice3(sK3,X0_45,X0_44)
% 0.95/0.99      | ~ r2_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X1_44)
% 0.95/0.99      | X0_45 != k3_xboole_0(X0_47,k1_xboole_0)
% 0.95/0.99      | X0_44 != X1_44 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1148]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1760,plain,
% 0.95/0.99      ( ~ r2_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
% 0.95/0.99      | r2_lattice3(sK3,k1_xboole_0,sK4)
% 0.95/0.99      | k1_xboole_0 != k3_xboole_0(iProver_bot,k1_xboole_0)
% 0.95/0.99      | sK4 != sK4 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1758]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_0,plain,
% 0.95/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 0.95/0.99      inference(cnf_transformation,[],[f29]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_3,plain,
% 0.95/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f31]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_175,plain,
% 0.95/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 0.95/0.99      | X3 != X1
% 0.95/0.99      | k1_xboole_0 != X2 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_176,plain,
% 0.95/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_175]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1134,plain,
% 0.95/0.99      ( ~ r2_hidden(X0_44,k3_xboole_0(X0_47,k1_xboole_0)) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_176]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1688,plain,
% 0.95/0.99      ( ~ r2_hidden(sK2(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1134]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1694,plain,
% 0.95/0.99      ( ~ r2_hidden(sK2(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1688]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_9,plain,
% 0.95/0.99      ( r2_lattice3(X0,X1,X2)
% 0.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.95/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 0.95/0.99      | ~ l1_orders_2(X0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f38]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_14,negated_conjecture,
% 0.95/0.99      ( l1_orders_2(sK3) ),
% 0.95/0.99      inference(cnf_transformation,[],[f40]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_225,plain,
% 0.95/0.99      ( r2_lattice3(X0,X1,X2)
% 0.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.95/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 0.95/0.99      | sK3 != X0 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_226,plain,
% 0.95/0.99      ( r2_lattice3(sK3,X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK2(sK3,X0,X1),X0) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_225]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1131,plain,
% 0.95/0.99      ( r2_lattice3(sK3,X0_45,X0_44)
% 0.95/0.99      | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK2(sK3,X0_45,X0_44),X0_45) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_226]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1687,plain,
% 0.95/0.99      ( r2_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44)
% 0.95/0.99      | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK2(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1131]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1690,plain,
% 0.95/0.99      ( r2_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
% 0.95/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK2(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1687]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1142,plain,
% 0.95/0.99      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 0.95/0.99      theory(equality) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1654,plain,
% 0.95/0.99      ( X0_45 != X1_45
% 0.95/0.99      | X0_45 = k3_xboole_0(X0_47,k1_xboole_0)
% 0.95/0.99      | k3_xboole_0(X0_47,k1_xboole_0) != X1_45 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1142]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1655,plain,
% 0.95/0.99      ( k3_xboole_0(iProver_bot,k1_xboole_0) != k1_xboole_0
% 0.95/0.99      | k1_xboole_0 = k3_xboole_0(iProver_bot,k1_xboole_0)
% 0.95/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1654]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1145,plain,
% 0.95/0.99      ( ~ r1_lattice3(X0_43,X0_45,X0_44)
% 0.95/0.99      | r1_lattice3(X0_43,X1_45,X1_44)
% 0.95/0.99      | X1_45 != X0_45
% 0.95/0.99      | X1_44 != X0_44 ),
% 0.95/0.99      theory(equality) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1584,plain,
% 0.95/0.99      ( r1_lattice3(sK3,X0_45,X0_44)
% 0.95/0.99      | ~ r1_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X1_44)
% 0.95/0.99      | X0_45 != k3_xboole_0(X0_47,k1_xboole_0)
% 0.95/0.99      | X0_44 != X1_44 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1145]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1586,plain,
% 0.95/0.99      ( ~ r1_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
% 0.95/0.99      | r1_lattice3(sK3,k1_xboole_0,sK4)
% 0.95/0.99      | k1_xboole_0 != k3_xboole_0(iProver_bot,k1_xboole_0)
% 0.95/0.99      | sK4 != sK4 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1584]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_5,plain,
% 0.95/0.99      ( r1_lattice3(X0,X1,X2)
% 0.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.95/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 0.95/0.99      | ~ l1_orders_2(X0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f34]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_291,plain,
% 0.95/0.99      ( r1_lattice3(X0,X1,X2)
% 0.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.95/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 0.95/0.99      | sK3 != X0 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_292,plain,
% 0.95/0.99      ( r1_lattice3(sK3,X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK1(sK3,X0,X1),X0) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1127,plain,
% 0.95/0.99      ( r1_lattice3(sK3,X0_45,X0_44)
% 0.95/0.99      | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK1(sK3,X0_45,X0_44),X0_45) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_292]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1546,plain,
% 0.95/0.99      ( r1_lattice3(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44)
% 0.95/0.99      | ~ m1_subset_1(X0_44,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK1(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1127]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1552,plain,
% 0.95/0.99      ( r1_lattice3(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4)
% 0.95/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 0.95/0.99      | r2_hidden(sK1(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1546]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1545,plain,
% 0.95/0.99      ( ~ r2_hidden(sK1(sK3,k3_xboole_0(X0_47,k1_xboole_0),X0_44),k3_xboole_0(X0_47,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1134]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1548,plain,
% 0.95/0.99      ( ~ r2_hidden(sK1(sK3,k3_xboole_0(iProver_bot,k1_xboole_0),sK4),k3_xboole_0(iProver_bot,k1_xboole_0)) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1545]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_2,plain,
% 0.95/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.95/0.99      inference(cnf_transformation,[],[f30]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1138,plain,
% 0.95/0.99      ( k3_xboole_0(X0_47,k1_xboole_0) = k1_xboole_0 ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1158,plain,
% 0.95/0.99      ( k3_xboole_0(iProver_bot,k1_xboole_0) = k1_xboole_0 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1138]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1141,plain,( X0_45 = X0_45 ),theory(equality) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1157,plain,
% 0.95/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1140,plain,( X0_44 = X0_44 ),theory(equality) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1156,plain,
% 0.95/0.99      ( sK4 = sK4 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_12,negated_conjecture,
% 0.95/0.99      ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
% 0.95/0.99      | ~ r1_lattice3(sK3,k1_xboole_0,sK4) ),
% 0.95/0.99      inference(cnf_transformation,[],[f42]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_13,negated_conjecture,
% 0.95/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 0.95/0.99      inference(cnf_transformation,[],[f41]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(contradiction,plain,
% 0.95/0.99      ( $false ),
% 0.95/0.99      inference(minisat,
% 0.95/0.99                [status(thm)],
% 0.95/0.99                [c_1760,c_1694,c_1690,c_1655,c_1586,c_1552,c_1548,c_1158,
% 0.95/0.99                 c_1157,c_1156,c_12,c_13]) ).
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  ------                               Statistics
% 0.95/0.99  
% 0.95/0.99  ------ General
% 0.95/0.99  
% 0.95/0.99  abstr_ref_over_cycles:                  0
% 0.95/0.99  abstr_ref_under_cycles:                 0
% 0.95/0.99  gc_basic_clause_elim:                   0
% 0.95/0.99  forced_gc_time:                         0
% 0.95/0.99  parsing_time:                           0.009
% 0.95/0.99  unif_index_cands_time:                  0.
% 0.95/0.99  unif_index_add_time:                    0.
% 0.95/0.99  orderings_time:                         0.
% 0.95/0.99  out_proof_time:                         0.009
% 0.95/0.99  total_time:                             0.081
% 0.95/0.99  num_of_symbols:                         48
% 0.95/0.99  num_of_terms:                           1444
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing
% 0.95/0.99  
% 0.95/0.99  num_of_splits:                          0
% 0.95/0.99  num_of_split_atoms:                     0
% 0.95/0.99  num_of_reused_defs:                     0
% 0.95/0.99  num_eq_ax_congr_red:                    32
% 0.95/0.99  num_of_sem_filtered_clauses:            1
% 0.95/0.99  num_of_subtypes:                        5
% 0.95/0.99  monotx_restored_types:                  0
% 0.95/0.99  sat_num_of_epr_types:                   0
% 0.95/0.99  sat_num_of_non_cyclic_types:            0
% 0.95/0.99  sat_guarded_non_collapsed_types:        0
% 0.95/0.99  num_pure_diseq_elim:                    0
% 0.95/0.99  simp_replaced_by:                       0
% 0.95/0.99  res_preprocessed:                       73
% 0.95/0.99  prep_upred:                             0
% 0.95/0.99  prep_unflattend:                        64
% 0.95/0.99  smt_new_axioms:                         0
% 0.95/0.99  pred_elim_cands:                        5
% 0.95/0.99  pred_elim:                              2
% 0.95/0.99  pred_elim_cl:                           2
% 0.95/0.99  pred_elim_cycles:                       8
% 0.95/0.99  merged_defs:                            0
% 0.95/0.99  merged_defs_ncl:                        0
% 0.95/0.99  bin_hyper_res:                          0
% 0.95/0.99  prep_cycles:                            4
% 0.95/0.99  pred_elim_time:                         0.015
% 0.95/0.99  splitting_time:                         0.
% 0.95/0.99  sem_filter_time:                        0.
% 0.95/0.99  monotx_time:                            0.
% 0.95/0.99  subtype_inf_time:                       0.
% 0.95/0.99  
% 0.95/0.99  ------ Problem properties
% 0.95/0.99  
% 0.95/0.99  clauses:                                13
% 0.95/0.99  conjectures:                            2
% 0.95/0.99  epr:                                    1
% 0.95/0.99  horn:                                   9
% 0.95/0.99  ground:                                 2
% 0.95/0.99  unary:                                  3
% 0.95/0.99  binary:                                 2
% 0.95/0.99  lits:                                   35
% 0.95/0.99  lits_eq:                                1
% 0.95/0.99  fd_pure:                                0
% 0.95/0.99  fd_pseudo:                              0
% 0.95/0.99  fd_cond:                                0
% 0.95/0.99  fd_pseudo_cond:                         0
% 0.95/0.99  ac_symbols:                             0
% 0.95/0.99  
% 0.95/0.99  ------ Propositional Solver
% 0.95/0.99  
% 0.95/0.99  prop_solver_calls:                      26
% 0.95/0.99  prop_fast_solver_calls:                 654
% 0.95/0.99  smt_solver_calls:                       0
% 0.95/0.99  smt_fast_solver_calls:                  0
% 0.95/0.99  prop_num_of_clauses:                    357
% 0.95/0.99  prop_preprocess_simplified:             2352
% 0.95/0.99  prop_fo_subsumed:                       17
% 0.95/0.99  prop_solver_time:                       0.
% 0.95/0.99  smt_solver_time:                        0.
% 0.95/0.99  smt_fast_solver_time:                   0.
% 0.95/0.99  prop_fast_solver_time:                  0.
% 0.95/0.99  prop_unsat_core_time:                   0.
% 0.95/0.99  
% 0.95/0.99  ------ QBF
% 0.95/0.99  
% 0.95/0.99  qbf_q_res:                              0
% 0.95/0.99  qbf_num_tautologies:                    0
% 0.95/0.99  qbf_prep_cycles:                        0
% 0.95/0.99  
% 0.95/0.99  ------ BMC1
% 0.95/0.99  
% 0.95/0.99  bmc1_current_bound:                     -1
% 0.95/0.99  bmc1_last_solved_bound:                 -1
% 0.95/0.99  bmc1_unsat_core_size:                   -1
% 0.95/0.99  bmc1_unsat_core_parents_size:           -1
% 0.95/0.99  bmc1_merge_next_fun:                    0
% 0.95/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation
% 0.95/0.99  
% 0.95/0.99  inst_num_of_clauses:                    64
% 0.95/0.99  inst_num_in_passive:                    12
% 0.95/0.99  inst_num_in_active:                     51
% 0.95/0.99  inst_num_in_unprocessed:                0
% 0.95/0.99  inst_num_of_loops:                      64
% 0.95/0.99  inst_num_of_learning_restarts:          0
% 0.95/0.99  inst_num_moves_active_passive:          9
% 0.95/0.99  inst_lit_activity:                      0
% 0.95/0.99  inst_lit_activity_moves:                0
% 0.95/0.99  inst_num_tautologies:                   0
% 0.95/0.99  inst_num_prop_implied:                  0
% 0.95/0.99  inst_num_existing_simplified:           0
% 0.95/0.99  inst_num_eq_res_simplified:             0
% 0.95/0.99  inst_num_child_elim:                    0
% 0.95/0.99  inst_num_of_dismatching_blockings:      2
% 0.95/0.99  inst_num_of_non_proper_insts:           33
% 0.95/0.99  inst_num_of_duplicates:                 0
% 0.95/0.99  inst_inst_num_from_inst_to_res:         0
% 0.95/0.99  inst_dismatching_checking_time:         0.
% 0.95/0.99  
% 0.95/0.99  ------ Resolution
% 0.95/0.99  
% 0.95/0.99  res_num_of_clauses:                     0
% 0.95/0.99  res_num_in_passive:                     0
% 0.95/0.99  res_num_in_active:                      0
% 0.95/0.99  res_num_of_loops:                       77
% 0.95/0.99  res_forward_subset_subsumed:            0
% 0.95/0.99  res_backward_subset_subsumed:           0
% 0.95/0.99  res_forward_subsumed:                   0
% 0.95/0.99  res_backward_subsumed:                  0
% 0.95/0.99  res_forward_subsumption_resolution:     3
% 0.95/0.99  res_backward_subsumption_resolution:    0
% 0.95/0.99  res_clause_to_clause_subsumption:       26
% 0.95/0.99  res_orphan_elimination:                 0
% 0.95/0.99  res_tautology_del:                      0
% 0.95/0.99  res_num_eq_res_simplified:              0
% 0.95/0.99  res_num_sel_changes:                    0
% 0.95/0.99  res_moves_from_active_to_pass:          0
% 0.95/0.99  
% 0.95/0.99  ------ Superposition
% 0.95/0.99  
% 0.95/0.99  sup_time_total:                         0.
% 0.95/0.99  sup_time_generating:                    0.
% 0.95/0.99  sup_time_sim_full:                      0.
% 0.95/0.99  sup_time_sim_immed:                     0.
% 0.95/0.99  
% 0.95/0.99  sup_num_of_clauses:                     17
% 0.95/0.99  sup_num_in_active:                      12
% 0.95/0.99  sup_num_in_passive:                     5
% 0.95/0.99  sup_num_of_loops:                       12
% 0.95/0.99  sup_fw_superposition:                   4
% 0.95/0.99  sup_bw_superposition:                   0
% 0.95/0.99  sup_immediate_simplified:               0
% 0.95/0.99  sup_given_eliminated:                   0
% 0.95/0.99  comparisons_done:                       0
% 0.95/0.99  comparisons_avoided:                    0
% 0.95/0.99  
% 0.95/0.99  ------ Simplifications
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  sim_fw_subset_subsumed:                 0
% 0.95/0.99  sim_bw_subset_subsumed:                 0
% 0.95/0.99  sim_fw_subsumed:                        0
% 0.95/0.99  sim_bw_subsumed:                        0
% 0.95/0.99  sim_fw_subsumption_res:                 0
% 0.95/0.99  sim_bw_subsumption_res:                 0
% 0.95/0.99  sim_tautology_del:                      0
% 0.95/0.99  sim_eq_tautology_del:                   0
% 0.95/0.99  sim_eq_res_simp:                        0
% 0.95/0.99  sim_fw_demodulated:                     0
% 0.95/0.99  sim_bw_demodulated:                     0
% 0.95/0.99  sim_light_normalised:                   1
% 0.95/0.99  sim_joinable_taut:                      0
% 0.95/0.99  sim_joinable_simp:                      0
% 0.95/0.99  sim_ac_normalised:                      0
% 0.95/0.99  sim_smt_subsumption:                    0
% 0.95/0.99  
%------------------------------------------------------------------------------
