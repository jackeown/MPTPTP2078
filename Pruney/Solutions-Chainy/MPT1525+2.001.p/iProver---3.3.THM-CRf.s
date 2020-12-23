%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:23 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  217 (2252 expanded)
%              Number of clauses        :  167 ( 621 expanded)
%              Number of leaves         :   12 ( 600 expanded)
%              Depth                    :   26
%              Number of atoms          :  859 (11524 expanded)
%              Number of equality atoms :  313 (2290 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( ( v3_lattice3(X0)
              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
           => v3_lattice3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( ( v3_lattice3(X0)
                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
             => v3_lattice3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ~ v3_lattice3(sK5)
        & v3_lattice3(X0)
        & g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_lattice3(X1)
            & v3_lattice3(X0)
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(sK4)
          & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ v3_lattice3(sK5)
    & v3_lattice3(sK4)
    & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    & l1_orders_2(sK5)
    & l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f29,f28])).

fof(f46,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,sK2(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK2(X0,X4))
        & m1_subset_1(sK2(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X2))
        & r2_lattice3(X0,X1,sK1(X0,X2))
        & m1_subset_1(sK1(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,sK0(X0),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,sK0(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_orders_2(X0,X2,sK1(X0,X2))
                & r2_lattice3(X0,sK0(X0),sK1(X0,X2))
                & m1_subset_1(sK1(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK0(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_orders_2(X0,sK2(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK2(X0,X4))
              & m1_subset_1(sK2(X0,X4),u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).

fof(f40,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | r2_lattice3(X0,sK0(X0),sK1(X0,X2))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ~ v3_lattice3(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | m1_subset_1(sK1(X0,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X6,X4,X0] :
      ( r1_orders_2(X0,sK2(X0,X4),X6)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    v3_lattice3(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK2(X0,X4),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | ~ r1_orders_2(X0,X2,sK1(X0,X2))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK2(X0,X4))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1117,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_1118,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1117])).

cnf(c_2430,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_17,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2446,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2793,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2446])).

cnf(c_2,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_53,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2794,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2446])).

cnf(c_2811,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2794])).

cnf(c_2932,plain,
    ( u1_struct_0(sK4) = X0
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_19,c_53,c_2811])).

cnf(c_2933,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(renaming,[status(thm)],[c_2932])).

cnf(c_2938,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK4) ),
    inference(equality_resolution,[status(thm)],[c_2933])).

cnf(c_3366,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2430,c_2938])).

cnf(c_6,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1004,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v3_lattice3(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_1005,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v3_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_15,negated_conjecture,
    ( ~ v3_lattice3(sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_752,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_753,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
    | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_18])).

cnf(c_758,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_757])).

cnf(c_1007,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
    | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_18,c_753])).

cnf(c_1008,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1007])).

cnf(c_2444,plain,
    ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_915,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_916,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r1_orders_2(sK5,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_2439,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,X2,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_3773,plain,
    ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | r1_orders_2(sK5,X1,sK1(sK5,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,sK0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2444,c_2439])).

cnf(c_21,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_731,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_732,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_733,plain,
    ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) = iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_4472,plain,
    ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,X1,sK1(sK5,X0)) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | r2_hidden(X1,sK0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3773,c_21,c_733])).

cnf(c_4473,plain,
    ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | r1_orders_2(sK5,X1,sK1(sK5,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,sK0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4472])).

cnf(c_13,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1102,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_1103,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1102])).

cnf(c_2431,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_3420,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2431,c_2938])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1045,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_1046,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
    inference(unflattening,[status(thm)],[c_1045])).

cnf(c_2434,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1046])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1217,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_1218,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) ),
    inference(unflattening,[status(thm)],[c_1217])).

cnf(c_2426,plain,
    ( r1_orders_2(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1218])).

cnf(c_3068,plain,
    ( r1_orders_2(sK4,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2938,c_2426])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2447,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2910,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2447])).

cnf(c_20,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_52,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_54,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_2911,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1
    | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2447])).

cnf(c_3050,plain,
    ( u1_orders_2(sK4) = X1
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2910,c_20,c_54,c_2911])).

cnf(c_3051,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1 ),
    inference(renaming,[status(thm)],[c_3050])).

cnf(c_3056,plain,
    ( u1_orders_2(sK5) = u1_orders_2(sK4) ),
    inference(equality_resolution,[status(thm)],[c_3051])).

cnf(c_4171,plain,
    ( r1_orders_2(sK4,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3068,c_3056])).

cnf(c_4179,plain,
    ( r1_orders_2(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_4171])).

cnf(c_4274,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),X2) = iProver_top
    | r1_orders_2(sK5,sK3(sK4,X0,X1),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3420,c_4179])).

cnf(c_5082,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X2),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4473,c_4274])).

cnf(c_5821,plain,
    ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
    | r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(sK1(sK5,X2),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5082,c_3420])).

cnf(c_5822,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X2),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5821])).

cnf(c_987,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | v3_lattice3(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_988,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v3_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_736,plain,
    ( m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_18])).

cnf(c_737,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_736])).

cnf(c_990,plain,
    ( m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_18,c_732])).

cnf(c_991,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_990])).

cnf(c_2445,plain,
    ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_5834,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5822,c_2445])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1132,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_1133,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ r1_orders_2(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1132])).

cnf(c_2429,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_3069,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2938,c_2429])).

cnf(c_5838,plain,
    ( r2_lattice3(sK4,X0,sK1(sK5,X1)) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X1),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK1(sK5,X1)),sK0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_3069])).

cnf(c_6017,plain,
    ( r2_lattice3(sK4,X0,sK1(sK5,X1)) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK1(sK5,X1)),sK0(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5838,c_2445])).

cnf(c_6021,plain,
    ( r2_lattice3(sK4,sK0(sK5),sK1(sK5,X0)) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3366,c_6017])).

cnf(c_6026,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | r2_lattice3(sK4,sK0(sK5),sK1(sK5,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6021,c_21,c_733])).

cnf(c_6027,plain,
    ( r2_lattice3(sK4,sK0(sK5),sK1(sK5,X0)) = iProver_top
    | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6026])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK2(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1169,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK2(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_1170,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,sK2(sK4,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1169])).

cnf(c_16,negated_conjecture,
    ( v3_lattice3(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_824,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK2(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_825,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,sK2(sK4,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_829,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_orders_2(sK4,sK2(sK4,X0),X1)
    | ~ r2_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_825,c_19])).

cnf(c_830,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,sK2(sK4,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_829])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_orders_2(sK4,sK2(sK4,X0),X1)
    | ~ r2_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_19,c_825])).

cnf(c_1173,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,sK2(sK4,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1172])).

cnf(c_2440,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK4,sK2(sK4,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_3070,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK4,sK2(sK4,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2938,c_2440])).

cnf(c_10,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1147,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | ~ v3_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_1148,plain,
    ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ v3_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1147])).

cnf(c_794,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_795,plain,
    ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_1150,plain,
    ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1148,c_19,c_795])).

cnf(c_2442,plain,
    ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1150])).

cnf(c_3072,plain,
    ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2938,c_2442])).

cnf(c_1199,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_1200,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) ),
    inference(unflattening,[status(thm)],[c_1199])).

cnf(c_2427,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_3354,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2427,c_2938,c_3056])).

cnf(c_1063,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_1064,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_2433,plain,
    ( r1_orders_2(sK5,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_3686,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK5,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3354,c_2433])).

cnf(c_4076,plain,
    ( r1_orders_2(sK4,sK2(sK4,X0),X1) != iProver_top
    | r1_orders_2(sK5,sK2(sK4,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3072,c_3686])).

cnf(c_4630,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK5,sK2(sK4,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_4076])).

cnf(c_5,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ r1_orders_2(X0,X1,sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1021,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ r1_orders_2(X0,X1,sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v3_lattice3(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_1022,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v3_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_1021])).

cnf(c_773,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ r1_orders_2(X0,X1,sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_774,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
    | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_774,c_18])).

cnf(c_779,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_778])).

cnf(c_1024,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
    | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1022,c_18,c_774])).

cnf(c_1025,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),X0)
    | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1024])).

cnf(c_2443,plain,
    ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
    | r1_orders_2(sK5,X0,sK1(sK5,X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_4744,plain,
    ( r2_lattice3(sK4,X0,sK1(sK5,sK2(sK4,X0))) != iProver_top
    | r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0)) != iProver_top
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,sK2(sK4,X0)),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4630,c_2443])).

cnf(c_4405,plain,
    ( ~ r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0))
    | ~ m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,sK2(sK4,X0)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_4406,plain,
    ( r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0)) != iProver_top
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,sK2(sK4,X0)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4405])).

cnf(c_4828,plain,
    ( r2_lattice3(sK4,X0,sK1(sK5,sK2(sK4,X0))) != iProver_top
    | r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4744,c_3072,c_4406])).

cnf(c_6036,plain,
    ( r2_lattice3(sK5,sK0(sK5),sK2(sK4,sK0(sK5))) != iProver_top
    | m1_subset_1(sK2(sK4,sK0(sK5)),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6027,c_4828])).

cnf(c_951,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_952,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(sK3(sK5,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_951])).

cnf(c_2437,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1))
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1158,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1))
    | ~ v3_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_1159,plain,
    ( r2_lattice3(sK4,X0,sK2(sK4,X0))
    | ~ v3_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1158])).

cnf(c_809,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_810,plain,
    ( r2_lattice3(sK4,X0,sK2(sK4,X0))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_1161,plain,
    ( r2_lattice3(sK4,X0,sK2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1159,c_19,c_810])).

cnf(c_2441,plain,
    ( r2_lattice3(sK4,X0,sK2(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_1081,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_1082,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_1081])).

cnf(c_2432,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK4,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1082])).

cnf(c_3754,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK4,X2,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2432,c_2938])).

cnf(c_3763,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK4,X1),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2441,c_3754])).

cnf(c_4327,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3763,c_3072])).

cnf(c_936,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_937,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_936])).

cnf(c_2438,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_4035,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK5,X0,X1),X2) != iProver_top
    | r1_orders_2(sK5,sK3(sK5,X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_3686])).

cnf(c_4560,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK4,X2),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4035])).

cnf(c_938,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_5185,plain,
    ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
    | r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(sK2(sK4,X2),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4560,c_938])).

cnf(c_5186,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK4,X2),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5185])).

cnf(c_5196,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5186,c_3072])).

cnf(c_966,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_967,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,sK3(sK5,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_966])).

cnf(c_2436,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,sK3(sK5,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_5200,plain,
    ( r2_lattice3(sK5,X0,sK2(sK4,X1)) = iProver_top
    | m1_subset_1(sK2(sK4,X1),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0,sK2(sK4,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_2436])).

cnf(c_5228,plain,
    ( r2_lattice3(sK5,X0,sK2(sK4,X1)) = iProver_top
    | r2_hidden(sK3(sK5,X0,sK2(sK4,X1)),X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5200,c_3072])).

cnf(c_5232,plain,
    ( r2_lattice3(sK5,X0,sK2(sK4,X0)) = iProver_top
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_5228])).

cnf(c_5337,plain,
    ( r2_lattice3(sK5,X0,sK2(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5232,c_3072])).

cnf(c_6279,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6036,c_3072,c_5337])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.59/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.99  
% 2.59/0.99  ------  iProver source info
% 2.59/0.99  
% 2.59/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.99  git: non_committed_changes: false
% 2.59/0.99  git: last_make_outside_of_git: false
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     num_symb
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       true
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  ------ Parsing...
% 2.59/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.99  ------ Proving...
% 2.59/0.99  ------ Problem Properties 
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  clauses                                 24
% 2.59/0.99  conjectures                             1
% 2.59/0.99  EPR                                     1
% 2.59/0.99  Horn                                    20
% 2.59/0.99  unary                                   6
% 2.59/0.99  binary                                  0
% 2.59/0.99  lits                                    68
% 2.59/0.99  lits eq                                 6
% 2.59/0.99  fd_pure                                 0
% 2.59/0.99  fd_pseudo                               0
% 2.59/0.99  fd_cond                                 0
% 2.59/0.99  fd_pseudo_cond                          2
% 2.59/0.99  AC symbols                              0
% 2.59/0.99  
% 2.59/0.99  ------ Schedule dynamic 5 is on 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  Current options:
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     none
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       false
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ Proving...
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS status Theorem for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99   Resolution empty clause
% 2.59/0.99  
% 2.59/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  fof(f5,axiom,(
% 2.59/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f13,plain,(
% 2.59/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f5])).
% 2.59/0.99  
% 2.59/0.99  fof(f14,plain,(
% 2.59/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(flattening,[],[f13])).
% 2.59/0.99  
% 2.59/0.99  fof(f24,plain,(
% 2.59/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(nnf_transformation,[],[f14])).
% 2.59/0.99  
% 2.59/0.99  fof(f25,plain,(
% 2.59/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(rectify,[],[f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f26,plain,(
% 2.59/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f27,plain,(
% 2.59/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 2.59/0.99  
% 2.59/0.99  fof(f44,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f27])).
% 2.59/0.99  
% 2.59/0.99  fof(f6,conjecture,(
% 2.59/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ((v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) => v3_lattice3(X1))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f7,negated_conjecture,(
% 2.59/0.99    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ((v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) => v3_lattice3(X1))))),
% 2.59/0.99    inference(negated_conjecture,[],[f6])).
% 2.59/0.99  
% 2.59/0.99  fof(f15,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : ((~v3_lattice3(X1) & (v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f7])).
% 2.59/0.99  
% 2.59/0.99  fof(f16,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : (~v3_lattice3(X1) & v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 2.59/0.99    inference(flattening,[],[f15])).
% 2.59/0.99  
% 2.59/0.99  fof(f29,plain,(
% 2.59/0.99    ( ! [X0] : (? [X1] : (~v3_lattice3(X1) & v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) => (~v3_lattice3(sK5) & v3_lattice3(X0) & g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & l1_orders_2(sK5))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f28,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : (~v3_lattice3(X1) & v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (~v3_lattice3(X1) & v3_lattice3(sK4) & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(sK4))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f30,plain,(
% 2.59/0.99    (~v3_lattice3(sK5) & v3_lattice3(sK4) & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & l1_orders_2(sK5)) & l1_orders_2(sK4)),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f29,f28])).
% 2.59/0.99  
% 2.59/0.99  fof(f46,plain,(
% 2.59/0.99    l1_orders_2(sK4)),
% 2.59/0.99    inference(cnf_transformation,[],[f30])).
% 2.59/0.99  
% 2.59/0.99  fof(f48,plain,(
% 2.59/0.99    g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))),
% 2.59/0.99    inference(cnf_transformation,[],[f30])).
% 2.59/0.99  
% 2.59/0.99  fof(f3,axiom,(
% 2.59/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f10,plain,(
% 2.59/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.59/0.99    inference(ennf_transformation,[],[f3])).
% 2.59/0.99  
% 2.59/0.99  fof(f34,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f10])).
% 2.59/0.99  
% 2.59/0.99  fof(f2,axiom,(
% 2.59/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f9,plain,(
% 2.59/0.99    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f2])).
% 2.59/0.99  
% 2.59/0.99  fof(f33,plain,(
% 2.59/0.99    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f9])).
% 2.59/0.99  
% 2.59/0.99  fof(f4,axiom,(
% 2.59/0.99    ! [X0] : (l1_orders_2(X0) => (v3_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f11,plain,(
% 2.59/0.99    ! [X0] : ((v3_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f4])).
% 2.59/0.99  
% 2.59/0.99  fof(f12,plain,(
% 2.59/0.99    ! [X0] : ((v3_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(flattening,[],[f11])).
% 2.59/0.99  
% 2.59/0.99  fof(f18,plain,(
% 2.59/0.99    ! [X0] : (((v3_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_lattice3(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(nnf_transformation,[],[f12])).
% 2.59/0.99  
% 2.59/0.99  fof(f19,plain,(
% 2.59/0.99    ! [X0] : (((v3_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_orders_2(X0,X5,X6) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0))) & r2_lattice3(X0,X4,X5) & m1_subset_1(X5,u1_struct_0(X0))) | ~v3_lattice3(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(rectify,[],[f18])).
% 2.59/0.99  
% 2.59/0.99  fof(f22,plain,(
% 2.59/0.99    ! [X4,X0] : (? [X5] : (! [X6] : (r1_orders_2(X0,X5,X6) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0))) & r2_lattice3(X0,X4,X5) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_orders_2(X0,sK2(X0,X4),X6) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0))) & r2_lattice3(X0,X4,sK2(X0,X4)) & m1_subset_1(sK2(X0,X4),u1_struct_0(X0))))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f21,plain,(
% 2.59/0.99    ( ! [X1] : (! [X2,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X2)) & r2_lattice3(X0,X1,sK1(X0,X2)) & m1_subset_1(sK1(X0,X2),u1_struct_0(X0))))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f20,plain,(
% 2.59/0.99    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,sK0(X0),X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,sK0(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f23,plain,(
% 2.59/0.99    ! [X0] : (((v3_lattice3(X0) | ! [X2] : ((~r1_orders_2(X0,X2,sK1(X0,X2)) & r2_lattice3(X0,sK0(X0),sK1(X0,X2)) & m1_subset_1(sK1(X0,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,sK0(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_orders_2(X0,sK2(X0,X4),X6) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0))) & r2_lattice3(X0,X4,sK2(X0,X4)) & m1_subset_1(sK2(X0,X4),u1_struct_0(X0))) | ~v3_lattice3(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f40,plain,(
% 2.59/0.99    ( ! [X2,X0] : (v3_lattice3(X0) | r2_lattice3(X0,sK0(X0),sK1(X0,X2)) | ~r2_lattice3(X0,sK0(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f47,plain,(
% 2.59/0.99    l1_orders_2(sK5)),
% 2.59/0.99    inference(cnf_transformation,[],[f30])).
% 2.59/0.99  
% 2.59/0.99  fof(f50,plain,(
% 2.59/0.99    ~v3_lattice3(sK5)),
% 2.59/0.99    inference(cnf_transformation,[],[f30])).
% 2.59/0.99  
% 2.59/0.99  fof(f42,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f27])).
% 2.59/0.99  
% 2.59/0.99  fof(f39,plain,(
% 2.59/0.99    ( ! [X2,X0] : (v3_lattice3(X0) | m1_subset_1(sK1(X0,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,sK0(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f43,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f27])).
% 2.59/0.99  
% 2.59/0.99  fof(f1,axiom,(
% 2.59/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f8,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f1])).
% 2.59/0.99  
% 2.59/0.99  fof(f17,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.59/0.99    inference(nnf_transformation,[],[f8])).
% 2.59/0.99  
% 2.59/0.99  fof(f31,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f17])).
% 2.59/0.99  
% 2.59/0.99  fof(f32,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f17])).
% 2.59/0.99  
% 2.59/0.99  fof(f35,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f10])).
% 2.59/0.99  
% 2.59/0.99  fof(f45,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f27])).
% 2.59/0.99  
% 2.59/0.99  fof(f38,plain,(
% 2.59/0.99    ( ! [X6,X4,X0] : (r1_orders_2(X0,sK2(X0,X4),X6) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v3_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f49,plain,(
% 2.59/0.99    v3_lattice3(sK4)),
% 2.59/0.99    inference(cnf_transformation,[],[f30])).
% 2.59/0.99  
% 2.59/0.99  fof(f36,plain,(
% 2.59/0.99    ( ! [X4,X0] : (m1_subset_1(sK2(X0,X4),u1_struct_0(X0)) | ~v3_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f41,plain,(
% 2.59/0.99    ( ! [X2,X0] : (v3_lattice3(X0) | ~r1_orders_2(X0,X2,sK1(X0,X2)) | ~r2_lattice3(X0,sK0(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f37,plain,(
% 2.59/0.99    ( ! [X4,X0] : (r2_lattice3(X0,X4,sK2(X0,X4)) | ~v3_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  cnf(c_12,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_19,negated_conjecture,
% 2.59/0.99      ( l1_orders_2(sK4) ),
% 2.59/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1117,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1118,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,X1),X0) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1117]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2430,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_17,negated_conjecture,
% 2.59/0.99      ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
% 2.59/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.59/0.99      | X2 = X1
% 2.59/0.99      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2446,plain,
% 2.59/0.99      ( X0 = X1
% 2.59/0.99      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 2.59/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2793,plain,
% 2.59/0.99      ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
% 2.59/0.99      | u1_struct_0(sK4) = X0
% 2.59/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_17,c_2446]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2,plain,
% 2.59/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_53,plain,
% 2.59/0.99      ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
% 2.59/0.99      | ~ l1_orders_2(sK4) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2794,plain,
% 2.59/0.99      ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
% 2.59/0.99      | u1_struct_0(sK4) = X0
% 2.59/0.99      | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_17,c_2446]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2811,plain,
% 2.59/0.99      ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
% 2.59/0.99      | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
% 2.59/0.99      | u1_struct_0(sK4) = X0 ),
% 2.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2794]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2932,plain,
% 2.59/0.99      ( u1_struct_0(sK4) = X0
% 2.59/0.99      | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2793,c_19,c_53,c_2811]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2933,plain,
% 2.59/0.99      ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
% 2.59/0.99      | u1_struct_0(sK4) = X0 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_2932]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2938,plain,
% 2.59/0.99      ( u1_struct_0(sK5) = u1_struct_0(sK4) ),
% 2.59/0.99      inference(equality_resolution,[status(thm)],[c_2933]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3366,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_2430,c_2938]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | v3_lattice3(X0)
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_18,negated_conjecture,
% 2.59/0.99      ( l1_orders_2(sK5) ),
% 2.59/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1004,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | v3_lattice3(X0)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1005,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | v3_lattice3(sK5) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1004]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_15,negated_conjecture,
% 2.59/0.99      ( ~ v3_lattice3(sK5) ),
% 2.59/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_752,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | ~ l1_orders_2(X0)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_753,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ l1_orders_2(sK5) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_752]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_757,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
% 2.59/0.99      | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
% 2.59/0.99      inference(global_propositional_subsumption,[status(thm)],[c_753,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_758,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_757]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1007,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
% 2.59/0.99      | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1005,c_18,c_753]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1008,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_1007]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2444,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK1(sK5,X0)) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_14,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.59/0.99      | r1_orders_2(X0,X3,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/0.99      | ~ r2_hidden(X3,X1)
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_915,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.59/0.99      | r1_orders_2(X0,X3,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/0.99      | ~ r2_hidden(X3,X1)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_916,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,X0,X1)
% 2.59/0.99      | r1_orders_2(sK5,X2,X1)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.59/0.99      | ~ r2_hidden(X2,X0) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_915]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2439,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,X2,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3773,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,X1,sK1(sK5,X0)) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(X1,sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2444,c_2439]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_21,plain,
% 2.59/0.99      ( l1_orders_2(sK5) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_7,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 2.59/0.99      | v3_lattice3(X0)
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_731,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 2.59/0.99      | ~ l1_orders_2(X0)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_732,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
% 2.59/0.99      | ~ l1_orders_2(sK5) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_731]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_733,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) = iProver_top
% 2.59/0.99      | l1_orders_2(sK5) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4472,plain,
% 2.59/0.99      ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,X1,sK1(sK5,X0)) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | r2_hidden(X1,sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_3773,c_21,c_733]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4473,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,X1,sK1(sK5,X0)) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(X1,sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_4472]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_13,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1102,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1103,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1102]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2431,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1103]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3420,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK5)) = iProver_top ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_2431,c_2938]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1,plain,
% 2.59/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1045,plain,
% 2.59/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1046,plain,
% 2.59/0.99      ( ~ r1_orders_2(sK5,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1045]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2434,plain,
% 2.59/0.99      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1046]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_0,plain,
% 2.59/0.99      ( r1_orders_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1217,plain,
% 2.59/0.99      ( r1_orders_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1218,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.59/0.99      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1217]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2426,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1218]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3068,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2938,c_2426]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.59/0.99      | X2 = X0
% 2.59/0.99      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2447,plain,
% 2.59/0.99      ( X0 = X1
% 2.59/0.99      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 2.59/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2910,plain,
% 2.59/0.99      ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
% 2.59/0.99      | u1_orders_2(sK4) = X1
% 2.59/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_17,c_2447]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_20,plain,
% 2.59/0.99      ( l1_orders_2(sK4) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_52,plain,
% 2.59/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 2.59/0.99      | l1_orders_2(X0) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_54,plain,
% 2.59/0.99      ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
% 2.59/0.99      | l1_orders_2(sK4) != iProver_top ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_52]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2911,plain,
% 2.59/0.99      ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
% 2.59/0.99      | u1_orders_2(sK4) = X1
% 2.59/0.99      | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_17,c_2447]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3050,plain,
% 2.59/0.99      ( u1_orders_2(sK4) = X1
% 2.59/0.99      | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2910,c_20,c_54,c_2911]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3051,plain,
% 2.59/0.99      ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
% 2.59/0.99      | u1_orders_2(sK4) = X1 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_3050]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3056,plain,
% 2.59/0.99      ( u1_orders_2(sK5) = u1_orders_2(sK4) ),
% 2.59/0.99      inference(equality_resolution,[status(thm)],[c_3051]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4171,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) != iProver_top ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_3068,c_3056]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4179,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK5,X0,X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2434,c_4171]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4274,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),X2) = iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK3(sK4,X0,X1),X2) != iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3420,c_4179]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5082,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X2),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_4473,c_4274]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5821,plain,
% 2.59/0.99      ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
% 2.59/0.99      | r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X2),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5082,c_3420]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5822,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X2),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_5821]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_987,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 2.59/0.99      | v3_lattice3(X0)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_988,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
% 2.59/0.99      | v3_lattice3(sK5) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_987]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_736,plain,
% 2.59/0.99      ( m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
% 2.59/0.99      inference(global_propositional_subsumption,[status(thm)],[c_732,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_737,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_736]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_990,plain,
% 2.59/0.99      ( m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_988,c_18,c_732]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_991,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_990]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2445,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5834,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X2) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK1(sK5,X2)) = iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,X1),sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5822,c_2445]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_11,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1132,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1133,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | ~ r1_orders_2(sK4,sK3(sK4,X0,X1),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1132]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2429,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3069,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2938,c_2429]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5838,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK1(sK5,X1)) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X1),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,sK1(sK5,X1)),sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_5834,c_3069]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6017,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK1(sK5,X1)) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK4,X0,sK1(sK5,X1)),sK0(sK5)) != iProver_top ),
% 2.59/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5838,c_2445]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6021,plain,
% 2.59/0.99      ( r2_lattice3(sK4,sK0(sK5),sK1(sK5,X0)) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3366,c_6017]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6026,plain,
% 2.59/0.99      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | r2_lattice3(sK4,sK0(sK5),sK1(sK5,X0)) = iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_6021,c_21,c_733]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6027,plain,
% 2.59/0.99      ( r2_lattice3(sK4,sK0(sK5),sK1(sK5,X0)) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_6026]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_8,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.59/0.99      | r1_orders_2(X0,sK2(X0,X1),X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ v3_lattice3(X0)
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1169,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.59/0.99      | r1_orders_2(X0,sK2(X0,X1),X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ v3_lattice3(X0)
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1170,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | ~ v3_lattice3(sK4) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1169]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_16,negated_conjecture,
% 2.59/0.99      ( v3_lattice3(sK4) ),
% 2.59/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_824,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.59/0.99      | r1_orders_2(X0,sK2(X0,X1),X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ l1_orders_2(X0)
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_825,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | ~ l1_orders_2(sK4) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_824]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_829,plain,
% 2.59/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1)
% 2.59/0.99      | ~ r2_lattice3(sK4,X0,X1) ),
% 2.59/0.99      inference(global_propositional_subsumption,[status(thm)],[c_825,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_830,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_829]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1172,plain,
% 2.59/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1)
% 2.59/0.99      | ~ r2_lattice3(sK4,X0,X1) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1170,c_19,c_825]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1173,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_1172]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2440,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3070,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK2(sK4,X0),X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2938,c_2440]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_10,plain,
% 2.59/0.99      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
% 2.59/0.99      | ~ v3_lattice3(X0)
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1147,plain,
% 2.59/0.99      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
% 2.59/0.99      | ~ v3_lattice3(X0)
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1148,plain,
% 2.59/0.99      ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) | ~ v3_lattice3(sK4) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1147]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_794,plain,
% 2.59/0.99      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
% 2.59/0.99      | ~ l1_orders_2(X0)
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_795,plain,
% 2.59/0.99      ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) | ~ l1_orders_2(sK4) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_794]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1150,plain,
% 2.59/0.99      ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1148,c_19,c_795]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2442,plain,
% 2.59/0.99      ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1150]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3072,plain,
% 2.59/0.99      ( m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) = iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2938,c_2442]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1199,plain,
% 2.59/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1200,plain,
% 2.59/0.99      ( ~ r1_orders_2(sK4,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1199]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2427,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK4)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3354,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) = iProver_top ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_2427,c_2938,c_3056]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1063,plain,
% 2.59/0.99      ( r1_orders_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1064,plain,
% 2.59/0.99      ( r1_orders_2(sK5,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.59/0.99      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1063]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2433,plain,
% 2.59/0.99      ( r1_orders_2(sK5,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3686,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3354,c_2433]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4076,plain,
% 2.59/0.99      ( r1_orders_2(sK4,sK2(sK4,X0),X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK2(sK4,X0),X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3072,c_3686]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4630,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK2(sK4,X0),X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3070,c_4076]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | ~ r1_orders_2(X0,X1,sK1(X0,X1))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | v3_lattice3(X0)
% 2.59/0.99      | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1021,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | ~ r1_orders_2(X0,X1,sK1(X0,X1))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | v3_lattice3(X0)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1022,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | v3_lattice3(sK5) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1021]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_773,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,sK0(X0),X1)
% 2.59/0.99      | ~ r1_orders_2(X0,X1,sK1(X0,X1))
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.59/0.99      | ~ l1_orders_2(X0)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_774,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ l1_orders_2(sK5) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_773]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_778,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
% 2.59/0.99      | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
% 2.59/0.99      inference(global_propositional_subsumption,[status(thm)],[c_774,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_779,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_778]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1024,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.59/0.99      | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
% 2.59/0.99      | ~ r2_lattice3(sK5,sK0(sK5),X0) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1022,c_18,c_774]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1025,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),X0)
% 2.59/0.99      | ~ r1_orders_2(sK5,X0,sK1(sK5,X0))
% 2.59/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_1024]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2443,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),X0) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,X0,sK1(sK5,X0)) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4744,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK1(sK5,sK2(sK4,X0))) != iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,sK2(sK4,X0)),u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_4630,c_2443]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4405,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0))
% 2.59/0.99      | ~ m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5))
% 2.59/0.99      | m1_subset_1(sK1(sK5,sK2(sK4,X0)),u1_struct_0(sK5)) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_991]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4406,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK5,sK2(sK4,X0)),u1_struct_0(sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_4405]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4828,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK1(sK5,sK2(sK4,X0))) != iProver_top
% 2.59/0.99      | r2_lattice3(sK5,sK0(sK5),sK2(sK4,X0)) != iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_4744,c_3072,c_4406]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6036,plain,
% 2.59/0.99      ( r2_lattice3(sK5,sK0(sK5),sK2(sK4,sK0(sK5))) != iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,sK0(sK5)),u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_6027,c_4828]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_951,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_952,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,X1),X0) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_951]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2437,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,X1),X0) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_9,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,sK2(X0,X1)) | ~ v3_lattice3(X0) | ~ l1_orders_2(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1158,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,sK2(X0,X1)) | ~ v3_lattice3(X0) | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1159,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK2(sK4,X0)) | ~ v3_lattice3(sK4) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1158]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_809,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,sK2(X0,X1)) | ~ l1_orders_2(X0) | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_810,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK2(sK4,X0)) | ~ l1_orders_2(sK4) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_809]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1161,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK2(sK4,X0)) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1159,c_19,c_810]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2441,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,sK2(sK4,X0)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1081,plain,
% 2.59/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.59/0.99      | r1_orders_2(X0,X3,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/0.99      | ~ r2_hidden(X3,X1)
% 2.59/0.99      | sK4 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1082,plain,
% 2.59/0.99      ( ~ r2_lattice3(sK4,X0,X1)
% 2.59/0.99      | r1_orders_2(sK4,X2,X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.59/0.99      | ~ r2_hidden(X2,X0) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_1081]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2432,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,X2,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.59/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1082]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3754,plain,
% 2.59/0.99      ( r2_lattice3(sK4,X0,X1) != iProver_top
% 2.59/0.99      | r1_orders_2(sK4,X2,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_2432,c_2938]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3763,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,sK2(sK4,X1)) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X1),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2441,c_3754]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4327,plain,
% 2.59/0.99      ( r1_orders_2(sK4,X0,sK2(sK4,X1)) = iProver_top
% 2.59/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.59/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3763,c_3072]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_936,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_937,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.59/0.99      | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_936]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2438,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4035,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK4,sK3(sK5,X0,X1),X2) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK3(sK5,X0,X1),X2) = iProver_top
% 2.59/0.99      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2438,c_3686]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4560,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X2),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_4327,c_4035]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_938,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5185,plain,
% 2.59/0.99      ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
% 2.59/0.99      | r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X2),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4560,c_938]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5186,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X2),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_5185]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5196,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK3(sK5,X0,X1),sK2(sK4,X2)) = iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,X1),X2) != iProver_top ),
% 2.59/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5186,c_3072]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_966,plain,
% 2.59/0.99      ( r2_lattice3(X0,X1,X2)
% 2.59/0.99      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
% 2.59/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.59/0.99      | sK5 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_967,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1)
% 2.59/0.99      | ~ r1_orders_2(sK5,sK3(sK5,X0,X1),X1)
% 2.59/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_966]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2436,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 2.59/0.99      | r1_orders_2(sK5,sK3(sK5,X0,X1),X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5200,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,sK2(sK4,X1)) = iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X1),u1_struct_0(sK5)) != iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,sK2(sK4,X1)),X1) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_5196,c_2436]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5228,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,sK2(sK4,X1)) = iProver_top
% 2.59/0.99      | r2_hidden(sK3(sK5,X0,sK2(sK4,X1)),X1) != iProver_top ),
% 2.59/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5200,c_3072]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5232,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,sK2(sK4,X0)) = iProver_top
% 2.59/0.99      | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2437,c_5228]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5337,plain,
% 2.59/0.99      ( r2_lattice3(sK5,X0,sK2(sK4,X0)) = iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5232,c_3072]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6279,plain,
% 2.59/0.99      ( $false ),
% 2.59/0.99      inference(forward_subsumption_resolution,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_6036,c_3072,c_5337]) ).
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  ------                               Statistics
% 2.59/0.99  
% 2.59/0.99  ------ General
% 2.59/0.99  
% 2.59/0.99  abstr_ref_over_cycles:                  0
% 2.59/0.99  abstr_ref_under_cycles:                 0
% 2.59/0.99  gc_basic_clause_elim:                   0
% 2.59/0.99  forced_gc_time:                         0
% 2.59/0.99  parsing_time:                           0.025
% 2.59/0.99  unif_index_cands_time:                  0.
% 2.59/0.99  unif_index_add_time:                    0.
% 2.59/0.99  orderings_time:                         0.
% 2.59/0.99  out_proof_time:                         0.016
% 2.59/0.99  total_time:                             0.237
% 2.59/0.99  num_of_symbols:                         49
% 2.59/0.99  num_of_terms:                           5768
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing
% 2.59/0.99  
% 2.59/0.99  num_of_splits:                          0
% 2.59/0.99  num_of_split_atoms:                     0
% 2.59/0.99  num_of_reused_defs:                     0
% 2.59/0.99  num_eq_ax_congr_red:                    18
% 2.59/0.99  num_of_sem_filtered_clauses:            1
% 2.59/0.99  num_of_subtypes:                        0
% 2.59/0.99  monotx_restored_types:                  0
% 2.59/0.99  sat_num_of_epr_types:                   0
% 2.59/0.99  sat_num_of_non_cyclic_types:            0
% 2.59/0.99  sat_guarded_non_collapsed_types:        0
% 2.59/0.99  num_pure_diseq_elim:                    0
% 2.59/0.99  simp_replaced_by:                       0
% 2.59/0.99  res_preprocessed:                       99
% 2.59/0.99  prep_upred:                             0
% 2.59/0.99  prep_unflattend:                        124
% 2.59/0.99  smt_new_axioms:                         0
% 2.59/0.99  pred_elim_cands:                        6
% 2.59/0.99  pred_elim:                              2
% 2.59/0.99  pred_elim_cl:                           -4
% 2.59/0.99  pred_elim_cycles:                       7
% 2.59/0.99  merged_defs:                            0
% 2.59/0.99  merged_defs_ncl:                        0
% 2.59/0.99  bin_hyper_res:                          0
% 2.59/0.99  prep_cycles:                            3
% 2.59/0.99  pred_elim_time:                         0.034
% 2.59/0.99  splitting_time:                         0.
% 2.59/0.99  sem_filter_time:                        0.
% 2.59/0.99  monotx_time:                            0.
% 2.59/0.99  subtype_inf_time:                       0.
% 2.59/0.99  
% 2.59/0.99  ------ Problem properties
% 2.59/0.99  
% 2.59/0.99  clauses:                                24
% 2.59/0.99  conjectures:                            1
% 2.59/0.99  epr:                                    1
% 2.59/0.99  horn:                                   20
% 2.59/0.99  ground:                                 4
% 2.59/0.99  unary:                                  6
% 2.59/0.99  binary:                                 0
% 2.59/0.99  lits:                                   68
% 2.59/0.99  lits_eq:                                6
% 2.59/0.99  fd_pure:                                0
% 2.59/0.99  fd_pseudo:                              0
% 2.59/0.99  fd_cond:                                0
% 2.59/0.99  fd_pseudo_cond:                         2
% 2.59/0.99  ac_symbols:                             0
% 2.59/0.99  
% 2.59/0.99  ------ Propositional Solver
% 2.59/0.99  
% 2.59/0.99  prop_solver_calls:                      24
% 2.59/0.99  prop_fast_solver_calls:                 1370
% 2.59/0.99  smt_solver_calls:                       0
% 2.59/0.99  smt_fast_solver_calls:                  0
% 2.59/0.99  prop_num_of_clauses:                    1890
% 2.59/0.99  prop_preprocess_simplified:             5369
% 2.59/0.99  prop_fo_subsumed:                       35
% 2.59/0.99  prop_solver_time:                       0.
% 2.59/0.99  smt_solver_time:                        0.
% 2.59/0.99  smt_fast_solver_time:                   0.
% 2.59/0.99  prop_fast_solver_time:                  0.
% 2.59/0.99  prop_unsat_core_time:                   0.
% 2.59/0.99  
% 2.59/0.99  ------ QBF
% 2.59/0.99  
% 2.59/0.99  qbf_q_res:                              0
% 2.59/0.99  qbf_num_tautologies:                    0
% 2.59/0.99  qbf_prep_cycles:                        0
% 2.59/0.99  
% 2.59/0.99  ------ BMC1
% 2.59/0.99  
% 2.59/0.99  bmc1_current_bound:                     -1
% 2.59/0.99  bmc1_last_solved_bound:                 -1
% 2.59/0.99  bmc1_unsat_core_size:                   -1
% 2.59/0.99  bmc1_unsat_core_parents_size:           -1
% 2.59/0.99  bmc1_merge_next_fun:                    0
% 2.59/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation
% 2.59/0.99  
% 2.59/0.99  inst_num_of_clauses:                    528
% 2.59/0.99  inst_num_in_passive:                    174
% 2.59/0.99  inst_num_in_active:                     340
% 2.59/0.99  inst_num_in_unprocessed:                15
% 2.59/0.99  inst_num_of_loops:                      360
% 2.59/0.99  inst_num_of_learning_restarts:          0
% 2.59/0.99  inst_num_moves_active_passive:          15
% 2.59/0.99  inst_lit_activity:                      0
% 2.59/0.99  inst_lit_activity_moves:                0
% 2.59/0.99  inst_num_tautologies:                   0
% 2.59/0.99  inst_num_prop_implied:                  0
% 2.59/0.99  inst_num_existing_simplified:           0
% 2.59/0.99  inst_num_eq_res_simplified:             0
% 2.59/0.99  inst_num_child_elim:                    0
% 2.59/0.99  inst_num_of_dismatching_blockings:      338
% 2.59/0.99  inst_num_of_non_proper_insts:           926
% 2.59/0.99  inst_num_of_duplicates:                 0
% 2.59/0.99  inst_inst_num_from_inst_to_res:         0
% 2.59/0.99  inst_dismatching_checking_time:         0.
% 2.59/0.99  
% 2.59/0.99  ------ Resolution
% 2.59/0.99  
% 2.59/0.99  res_num_of_clauses:                     0
% 2.59/0.99  res_num_in_passive:                     0
% 2.59/0.99  res_num_in_active:                      0
% 2.59/0.99  res_num_of_loops:                       102
% 2.59/0.99  res_forward_subset_subsumed:            148
% 2.59/0.99  res_backward_subset_subsumed:           4
% 2.59/0.99  res_forward_subsumed:                   0
% 2.59/0.99  res_backward_subsumed:                  0
% 2.59/0.99  res_forward_subsumption_resolution:     7
% 2.59/0.99  res_backward_subsumption_resolution:    0
% 2.59/0.99  res_clause_to_clause_subsumption:       445
% 2.59/0.99  res_orphan_elimination:                 0
% 2.59/0.99  res_tautology_del:                      98
% 2.59/0.99  res_num_eq_res_simplified:              0
% 2.59/0.99  res_num_sel_changes:                    0
% 2.59/0.99  res_moves_from_active_to_pass:          0
% 2.59/0.99  
% 2.59/0.99  ------ Superposition
% 2.59/0.99  
% 2.59/0.99  sup_time_total:                         0.
% 2.59/0.99  sup_time_generating:                    0.
% 2.59/0.99  sup_time_sim_full:                      0.
% 2.59/0.99  sup_time_sim_immed:                     0.
% 2.59/0.99  
% 2.59/0.99  sup_num_of_clauses:                     70
% 2.59/0.99  sup_num_in_active:                      61
% 2.59/0.99  sup_num_in_passive:                     9
% 2.59/0.99  sup_num_of_loops:                       70
% 2.59/0.99  sup_fw_superposition:                   33
% 2.59/0.99  sup_bw_superposition:                   38
% 2.59/0.99  sup_immediate_simplified:               17
% 2.59/0.99  sup_given_eliminated:                   2
% 2.59/0.99  comparisons_done:                       0
% 2.59/0.99  comparisons_avoided:                    0
% 2.59/0.99  
% 2.59/0.99  ------ Simplifications
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  sim_fw_subset_subsumed:                 4
% 2.59/0.99  sim_bw_subset_subsumed:                 2
% 2.59/0.99  sim_fw_subsumed:                        13
% 2.59/0.99  sim_bw_subsumed:                        0
% 2.59/0.99  sim_fw_subsumption_res:                 21
% 2.59/0.99  sim_bw_subsumption_res:                 0
% 2.59/0.99  sim_tautology_del:                      2
% 2.59/0.99  sim_eq_tautology_del:                   7
% 2.59/0.99  sim_eq_res_simp:                        0
% 2.59/0.99  sim_fw_demodulated:                     0
% 2.59/0.99  sim_bw_demodulated:                     9
% 2.59/0.99  sim_light_normalised:                   6
% 2.59/0.99  sim_joinable_taut:                      0
% 2.59/0.99  sim_joinable_simp:                      0
% 2.59/0.99  sim_ac_normalised:                      0
% 2.59/0.99  sim_smt_subsumption:                    0
% 2.59/0.99  
%------------------------------------------------------------------------------
