%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:08 EST 2020

% Result     : Theorem 39.27s
% Output     : CNFRefutation 39.27s
% Verified   : 
% Statistics : Number of formulae       :  287 (2024 expanded)
%              Number of clauses        :  201 ( 530 expanded)
%              Number of leaves         :   23 ( 573 expanded)
%              Depth                    :   26
%              Number of atoms          : 1479 (11255 expanded)
%              Number of equality atoms :  197 ( 407 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   15 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_lattices(X0,X1,X2)
                   => r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
     => ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,sK5)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,sK4,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,sK4,X2)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(sK3,k3_lattices(sK3,X1,k16_lattice3(sK3,X2)),k16_lattice3(sK3,a_3_4_lattice3(sK3,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v4_lattice3(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f55,f54,f53])).

fof(f85,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f62,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
                  & r2_hidden(sK0(X0,X1,X2),X2)
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X3)
              & k3_lattices(X1,X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( r2_hidden(X5,X3)
              & k3_lattices(X1,X2,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X3)
          & k3_lattices(X1,X2,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK1(X0,X1,X2,X3),X3)
        & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2,X3),X3)
            & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
            & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK2(X0,X1,X2),X1)
        & r3_lattice3(X0,sK2(X0,X1,X2),X2)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK2(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK2(X0,X1,X2),X2)
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r3_lattices(X0,X4,X1)
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f59,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_lattices(X0,X2,X3)
                      & r3_lattices(X0,X1,X3) )
                   => r3_lattices(X0,k3_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X1,X2),X3)
                  | ~ r3_lattices(X0,X2,X3)
                  | ~ r3_lattices(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X1,X2),X3)
                  | ~ r3_lattices(X0,X2,X3)
                  | ~ r3_lattices(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X0,k3_lattices(X0,X1,X2),X3)
      | ~ r3_lattices(X0,X2,X3)
      | ~ r3_lattices(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(X0,X1,X2,X3),X3)
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

cnf(c_1383,plain,
    ( ~ r3_lattices(X0_53,X0_54,X1_54)
    | r3_lattices(X0_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_99295,plain,
    ( ~ r3_lattices(sK3,X0_54,X1_54)
    | r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
    | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != X1_54
    | sK4 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_141597,plain,
    ( ~ r3_lattices(sK3,X0_54,k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4))
    | r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
    | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4)
    | sK4 != X0_54 ),
    inference(instantiation,[status(thm)],[c_99295])).

cnf(c_141599,plain,
    ( r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ r3_lattices(sK3,sK4,k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4))
    | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_141597])).

cnf(c_1380,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_99747,plain,
    ( X0_54 != X1_54
    | X0_54 = k3_lattices(sK3,X2_54,X3_54)
    | k3_lattices(sK3,X2_54,X3_54) != X1_54 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_104230,plain,
    ( X0_54 != k3_lattices(sK3,X1_54,X2_54)
    | X0_54 = k3_lattices(sK3,X2_54,X1_54)
    | k3_lattices(sK3,X2_54,X1_54) != k3_lattices(sK3,X1_54,X2_54) ),
    inference(instantiation,[status(thm)],[c_99747])).

cnf(c_127276,plain,
    ( sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4)
    | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4) != k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_104230])).

cnf(c_11,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1038,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_1039,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,k3_lattices(sK3,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1038])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1043,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,k3_lattices(sK3,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1039,c_32,c_29])).

cnf(c_1044,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,k3_lattices(sK3,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1043])).

cnf(c_1359,plain,
    ( ~ r3_lattices(sK3,X0_54,X1_54)
    | r3_lattices(sK3,X0_54,k3_lattices(sK3,X2_54,X1_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1044])).

cnf(c_118271,plain,
    ( r3_lattices(sK3,sK4,k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4))
    | ~ r3_lattices(sK3,sK4,sK4)
    | ~ m1_subset_1(sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_1378,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_100957,plain,
    ( sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_506,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_9])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_510,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_2,c_1])).

cnf(c_13,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_594,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X3,X4,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v10_lattices(X3)
    | X0 != X3
    | X1 != X4
    | sK0(X0,X1,X2) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_510,c_13])).

cnf(c_595,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_15,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_15])).

cnf(c_600,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_599])).

cnf(c_966,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_600,c_31])).

cnf(c_967,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_966])).

cnf(c_971,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_32,c_29])).

cnf(c_1362,plain,
    ( r3_lattice3(sK3,X0_54,X0_55)
    | ~ r3_lattices(sK3,X0_54,sK0(sK3,X0_54,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_971])).

cnf(c_99051,plain,
    ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
    | ~ r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_2351,plain,
    ( X0_54 != X1_54
    | sK0(sK3,X2_54,X0_55) != X1_54
    | sK0(sK3,X2_54,X0_55) = X0_54 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_3315,plain,
    ( X0_54 != sK0(sK3,X1_54,X0_55)
    | sK0(sK3,X1_54,X0_55) = X0_54
    | sK0(sK3,X1_54,X0_55) != sK0(sK3,X1_54,X0_55) ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_67981,plain,
    ( sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) != sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) = k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55))
    | k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) != sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) ),
    inference(instantiation,[status(thm)],[c_3315])).

cnf(c_67982,plain,
    ( sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
    | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_67981])).

cnf(c_2572,plain,
    ( ~ r3_lattices(sK3,X0_54,X1_54)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),X2_54)
    | X2_54 != X1_54
    | k16_lattice3(sK3,sK5) != X0_54 ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_3303,plain,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),X1_54)
    | X1_54 != X0_54
    | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_6925,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
    | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,X1_54,X2_54))
    | X0_54 != k3_lattices(sK3,X1_54,X2_54)
    | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_3303])).

cnf(c_47105,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_6925])).

cnf(c_47125,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_47105])).

cnf(c_2557,plain,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,X1_54,X0_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_44576,plain,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,X0_54,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2557])).

cnf(c_44588,plain,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_44576])).

cnf(c_14,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1173,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_1174,plain,
    ( r3_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_29])).

cnf(c_1179,plain,
    ( r3_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1178])).

cnf(c_1354,plain,
    ( r3_lattice3(sK3,X0_54,X0_55)
    | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1179])).

cnf(c_1831,plain,
    ( r3_lattice3(sK3,X0_54,X0_55) = iProver_top
    | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1354])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_723,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_724,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_32,c_31,c_29])).

cnf(c_729,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_1370,plain,
    ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | k3_lattices(sK3,X1_54,sK1(X0_54,sK3,X1_54,X0_55)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_729])).

cnf(c_1813,plain,
    ( k3_lattices(sK3,X0_54,sK1(X1_54,sK3,X0_54,X0_55)) = X1_54
    | r2_hidden(X1_54,a_3_4_lattice3(sK3,X0_54,X0_55)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_2722,plain,
    ( k3_lattices(sK3,X0_54,sK1(sK0(sK3,X1_54,a_3_4_lattice3(sK3,X0_54,X0_55)),sK3,X0_54,X0_55)) = sK0(sK3,X1_54,a_3_4_lattice3(sK3,X0_54,X0_55))
    | r3_lattice3(sK3,X1_54,a_3_4_lattice3(sK3,X0_54,X0_55)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1831,c_1813])).

cnf(c_17,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1137,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_1138,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_1137])).

cnf(c_1142,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_29])).

cnf(c_25,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_804,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_805,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_809,plain,
    ( ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_805,c_32,c_31,c_29])).

cnf(c_810,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_809])).

cnf(c_1200,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1142,c_810])).

cnf(c_1353,plain,
    ( ~ r3_lattice3(sK3,X0_54,X0_55)
    | r3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1200])).

cnf(c_1832,plain,
    ( r3_lattice3(sK3,X0_54,X0_55) != iProver_top
    | r3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1353])).

cnf(c_3,plain,
    ( v5_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_12,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X3,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ v5_lattices(X0)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_398,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X3,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0) ),
    inference(resolution,[status(thm)],[c_3,c_12])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_402,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r3_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X3,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_4,c_2,c_1,c_0])).

cnf(c_403,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X3,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_1008,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X3,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_403,c_31])).

cnf(c_1009,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X2,X1)
    | r3_lattices(sK3,k3_lattices(sK3,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1008])).

cnf(c_1013,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X2,X1)
    | r3_lattices(sK3,k3_lattices(sK3,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1009,c_32,c_29])).

cnf(c_1014,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X2,X1)
    | r3_lattices(sK3,k3_lattices(sK3,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1013])).

cnf(c_1360,plain,
    ( ~ r3_lattices(sK3,X0_54,X1_54)
    | ~ r3_lattices(sK3,X2_54,X1_54)
    | r3_lattices(sK3,k3_lattices(sK3,X0_54,X2_54),X1_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1014])).

cnf(c_1825,plain,
    ( r3_lattices(sK3,X0_54,X1_54) != iProver_top
    | r3_lattices(sK3,X2_54,X1_54) != iProver_top
    | r3_lattices(sK3,k3_lattices(sK3,X0_54,X2_54),X1_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_27,negated_conjecture,
    ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1373,negated_conjecture,
    ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1810,plain,
    ( r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_3400,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
    | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1810])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1356,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1142])).

cnf(c_1447,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_1449,plain,
    ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_2230,plain,
    ( m1_subset_1(k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_2231,plain,
    ( m1_subset_1(k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2230])).

cnf(c_3481,plain,
    ( r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3400,c_37,c_1449,c_2231])).

cnf(c_3482,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
    | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3481])).

cnf(c_3818,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
    | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1832,c_3482])).

cnf(c_4199,plain,
    ( r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
    | r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3818,c_1449])).

cnf(c_4200,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
    | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4199])).

cnf(c_4205,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
    | r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1832,c_4200])).

cnf(c_36328,plain,
    ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
    | r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4205,c_37])).

cnf(c_36329,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
    | r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36328])).

cnf(c_36336,plain,
    ( k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
    | r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2722,c_36329])).

cnf(c_36359,plain,
    ( ~ r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_36336])).

cnf(c_22989,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ r3_lattices(sK3,k16_lattice3(sK3,X0_55),sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_22993,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_22989])).

cnf(c_2347,plain,
    ( sK0(sK3,X0_54,X0_55) = sK0(sK3,X0_54,X0_55) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_22656,plain,
    ( sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_22657,plain,
    ( sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_22656])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | r2_hidden(sK1(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_744,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | r2_hidden(sK1(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_745,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | r2_hidden(sK1(X0,sK3,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK1(X0,sK3,X1,X2),X2)
    | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_32,c_31,c_29])).

cnf(c_750,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | r2_hidden(sK1(X0,sK3,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_1369,plain,
    ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | r2_hidden(sK1(X0_54,sK3,X1_54,X0_55),X0_55)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_750])).

cnf(c_2389,plain,
    ( r2_hidden(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X0_55)
    | ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_19493,plain,
    ( r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
    | ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2389])).

cnf(c_19495,plain,
    ( r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
    | ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_19493])).

cnf(c_12841,plain,
    ( sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5))
    | sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3315])).

cnf(c_12842,plain,
    ( sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
    | sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_12841])).

cnf(c_8,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_538,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_542,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_8,c_2,c_1,c_0])).

cnf(c_16,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_624,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X3,X4,X5)
    | ~ r2_hidden(X6,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v10_lattices(X3)
    | X0 != X3
    | X1 != X4
    | X6 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_16])).

cnf(c_625,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_939,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_625,c_31])).

cnf(c_940,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_944,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_32,c_29])).

cnf(c_945,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_944])).

cnf(c_1363,plain,
    ( ~ r3_lattice3(sK3,X0_54,X0_55)
    | r3_lattices(sK3,X0_54,X1_54)
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_945])).

cnf(c_2551,plain,
    ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),X0_55)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
    | ~ r2_hidden(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_3585,plain,
    ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),X0_55)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55))
    | ~ r2_hidden(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X0_55)
    | ~ m1_subset_1(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2551])).

cnf(c_12678,plain,
    ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | ~ r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
    | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3585])).

cnf(c_12685,plain,
    ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | ~ r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
    | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_12678])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_702,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_703,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_707,plain,
    ( m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_32,c_31,c_29])).

cnf(c_708,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_707])).

cnf(c_1371,plain,
    ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | m1_subset_1(sK1(X0_54,sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_708])).

cnf(c_2032,plain,
    ( ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_7483,plain,
    ( ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_7485,plain,
    ( ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7483])).

cnf(c_1812,plain,
    ( r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(X0_54,sK3,X1_54,X0_55),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_7,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_7,c_6])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_368])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_1065,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_447,c_31])).

cnf(c_1066,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | k3_lattices(sK3,X0,X1) = k3_lattices(sK3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1065])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k3_lattices(sK3,X0,X1) = k3_lattices(sK3,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1066,c_32,c_29])).

cnf(c_1071,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k3_lattices(sK3,X1,X0) = k3_lattices(sK3,X0,X1) ),
    inference(renaming,[status(thm)],[c_1070])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | k3_lattices(sK3,X1_54,X0_54) = k3_lattices(sK3,X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_1071])).

cnf(c_1827,plain,
    ( k3_lattices(sK3,X0_54,X1_54) = k3_lattices(sK3,X1_54,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_2516,plain,
    ( k3_lattices(sK3,sK1(X0_54,sK3,X1_54,X0_55),X2_54) = k3_lattices(sK3,X2_54,sK1(X0_54,sK3,X1_54,X0_55))
    | r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1812,c_1827])).

cnf(c_5077,plain,
    ( k3_lattices(sK3,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X2_54) = k3_lattices(sK3,X2_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55))
    | r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1831,c_2516])).

cnf(c_5119,plain,
    ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK3))
    | k3_lattices(sK3,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X2_54) = k3_lattices(sK3,X2_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5077])).

cnf(c_5121,plain,
    ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4) = k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_5119])).

cnf(c_4206,plain,
    ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4205])).

cnf(c_2033,plain,
    ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_4149,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5))
    | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2033])).

cnf(c_4151,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
    | r2_hidden(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4149])).

cnf(c_2740,plain,
    ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) = sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2722])).

cnf(c_2742,plain,
    ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2740])).

cnf(c_2039,plain,
    ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
    | r2_hidden(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2033])).

cnf(c_2035,plain,
    ( ~ r2_hidden(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | m1_subset_1(sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_1448,plain,
    ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_10,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_477,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_10])).

cnf(c_481,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_10,c_2,c_1,c_0])).

cnf(c_987,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_481,c_31])).

cnf(c_988,plain,
    ( r3_lattices(sK3,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_992,plain,
    ( r3_lattices(sK3,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_32,c_29])).

cnf(c_1361,plain,
    ( r3_lattices(sK3,X0_54,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_992])).

cnf(c_1374,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1361])).

cnf(c_1435,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1375,plain,
    ( r3_lattices(sK3,X0_54,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1361])).

cnf(c_1432,plain,
    ( r3_lattices(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1376,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1361])).

cnf(c_26,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_191,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_17])).

cnf(c_789,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_30])).

cnf(c_790,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_794,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_32,c_31,c_29])).

cnf(c_1367,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_794])).

cnf(c_1413,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_1379,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1397,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_1396,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1386,plain,
    ( X0_55 != X1_55
    | k16_lattice3(X0_53,X0_55) = k16_lattice3(X0_53,X1_55) ),
    theory(equality)).

cnf(c_1393,plain,
    ( sK5 != sK5
    | k16_lattice3(sK3,sK5) = k16_lattice3(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_141599,c_127276,c_118271,c_100957,c_99051,c_67982,c_47125,c_44588,c_36359,c_22993,c_22657,c_19495,c_12842,c_12685,c_7485,c_5121,c_4206,c_4151,c_2742,c_2039,c_2035,c_1448,c_1435,c_1432,c_1376,c_1413,c_1397,c_1396,c_1393,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:07:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.27/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.27/5.49  
% 39.27/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.27/5.49  
% 39.27/5.49  ------  iProver source info
% 39.27/5.49  
% 39.27/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.27/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.27/5.49  git: non_committed_changes: false
% 39.27/5.49  git: last_make_outside_of_git: false
% 39.27/5.49  
% 39.27/5.49  ------ 
% 39.27/5.49  
% 39.27/5.49  ------ Input Options
% 39.27/5.49  
% 39.27/5.49  --out_options                           all
% 39.27/5.49  --tptp_safe_out                         true
% 39.27/5.49  --problem_path                          ""
% 39.27/5.49  --include_path                          ""
% 39.27/5.49  --clausifier                            res/vclausify_rel
% 39.27/5.49  --clausifier_options                    --mode clausify
% 39.27/5.49  --stdin                                 false
% 39.27/5.49  --stats_out                             all
% 39.27/5.49  
% 39.27/5.49  ------ General Options
% 39.27/5.49  
% 39.27/5.49  --fof                                   false
% 39.27/5.49  --time_out_real                         305.
% 39.27/5.49  --time_out_virtual                      -1.
% 39.27/5.49  --symbol_type_check                     false
% 39.27/5.49  --clausify_out                          false
% 39.27/5.49  --sig_cnt_out                           false
% 39.27/5.49  --trig_cnt_out                          false
% 39.27/5.49  --trig_cnt_out_tolerance                1.
% 39.27/5.49  --trig_cnt_out_sk_spl                   false
% 39.27/5.49  --abstr_cl_out                          false
% 39.27/5.49  
% 39.27/5.49  ------ Global Options
% 39.27/5.49  
% 39.27/5.49  --schedule                              default
% 39.27/5.49  --add_important_lit                     false
% 39.27/5.49  --prop_solver_per_cl                    1000
% 39.27/5.49  --min_unsat_core                        false
% 39.27/5.49  --soft_assumptions                      false
% 39.27/5.49  --soft_lemma_size                       3
% 39.27/5.49  --prop_impl_unit_size                   0
% 39.27/5.49  --prop_impl_unit                        []
% 39.27/5.49  --share_sel_clauses                     true
% 39.27/5.49  --reset_solvers                         false
% 39.27/5.49  --bc_imp_inh                            [conj_cone]
% 39.27/5.49  --conj_cone_tolerance                   3.
% 39.27/5.49  --extra_neg_conj                        none
% 39.27/5.49  --large_theory_mode                     true
% 39.27/5.49  --prolific_symb_bound                   200
% 39.27/5.49  --lt_threshold                          2000
% 39.27/5.49  --clause_weak_htbl                      true
% 39.27/5.49  --gc_record_bc_elim                     false
% 39.27/5.49  
% 39.27/5.49  ------ Preprocessing Options
% 39.27/5.49  
% 39.27/5.49  --preprocessing_flag                    true
% 39.27/5.49  --time_out_prep_mult                    0.1
% 39.27/5.49  --splitting_mode                        input
% 39.27/5.49  --splitting_grd                         true
% 39.27/5.49  --splitting_cvd                         false
% 39.27/5.49  --splitting_cvd_svl                     false
% 39.27/5.49  --splitting_nvd                         32
% 39.27/5.49  --sub_typing                            true
% 39.27/5.49  --prep_gs_sim                           true
% 39.27/5.49  --prep_unflatten                        true
% 39.27/5.49  --prep_res_sim                          true
% 39.27/5.49  --prep_upred                            true
% 39.27/5.49  --prep_sem_filter                       exhaustive
% 39.27/5.49  --prep_sem_filter_out                   false
% 39.27/5.49  --pred_elim                             true
% 39.27/5.49  --res_sim_input                         true
% 39.27/5.49  --eq_ax_congr_red                       true
% 39.27/5.49  --pure_diseq_elim                       true
% 39.27/5.49  --brand_transform                       false
% 39.27/5.49  --non_eq_to_eq                          false
% 39.27/5.49  --prep_def_merge                        true
% 39.27/5.49  --prep_def_merge_prop_impl              false
% 39.27/5.49  --prep_def_merge_mbd                    true
% 39.27/5.49  --prep_def_merge_tr_red                 false
% 39.27/5.49  --prep_def_merge_tr_cl                  false
% 39.27/5.49  --smt_preprocessing                     true
% 39.27/5.49  --smt_ac_axioms                         fast
% 39.27/5.49  --preprocessed_out                      false
% 39.27/5.49  --preprocessed_stats                    false
% 39.27/5.49  
% 39.27/5.49  ------ Abstraction refinement Options
% 39.27/5.49  
% 39.27/5.49  --abstr_ref                             []
% 39.27/5.49  --abstr_ref_prep                        false
% 39.27/5.49  --abstr_ref_until_sat                   false
% 39.27/5.49  --abstr_ref_sig_restrict                funpre
% 39.27/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.27/5.49  --abstr_ref_under                       []
% 39.27/5.49  
% 39.27/5.49  ------ SAT Options
% 39.27/5.49  
% 39.27/5.49  --sat_mode                              false
% 39.27/5.49  --sat_fm_restart_options                ""
% 39.27/5.49  --sat_gr_def                            false
% 39.27/5.49  --sat_epr_types                         true
% 39.27/5.49  --sat_non_cyclic_types                  false
% 39.27/5.49  --sat_finite_models                     false
% 39.27/5.49  --sat_fm_lemmas                         false
% 39.27/5.49  --sat_fm_prep                           false
% 39.27/5.49  --sat_fm_uc_incr                        true
% 39.27/5.49  --sat_out_model                         small
% 39.27/5.49  --sat_out_clauses                       false
% 39.27/5.49  
% 39.27/5.49  ------ QBF Options
% 39.27/5.49  
% 39.27/5.49  --qbf_mode                              false
% 39.27/5.49  --qbf_elim_univ                         false
% 39.27/5.49  --qbf_dom_inst                          none
% 39.27/5.49  --qbf_dom_pre_inst                      false
% 39.27/5.49  --qbf_sk_in                             false
% 39.27/5.49  --qbf_pred_elim                         true
% 39.27/5.49  --qbf_split                             512
% 39.27/5.49  
% 39.27/5.49  ------ BMC1 Options
% 39.27/5.49  
% 39.27/5.49  --bmc1_incremental                      false
% 39.27/5.49  --bmc1_axioms                           reachable_all
% 39.27/5.49  --bmc1_min_bound                        0
% 39.27/5.49  --bmc1_max_bound                        -1
% 39.27/5.49  --bmc1_max_bound_default                -1
% 39.27/5.49  --bmc1_symbol_reachability              true
% 39.27/5.49  --bmc1_property_lemmas                  false
% 39.27/5.49  --bmc1_k_induction                      false
% 39.27/5.49  --bmc1_non_equiv_states                 false
% 39.27/5.49  --bmc1_deadlock                         false
% 39.27/5.49  --bmc1_ucm                              false
% 39.27/5.49  --bmc1_add_unsat_core                   none
% 39.27/5.49  --bmc1_unsat_core_children              false
% 39.27/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.27/5.49  --bmc1_out_stat                         full
% 39.27/5.49  --bmc1_ground_init                      false
% 39.27/5.49  --bmc1_pre_inst_next_state              false
% 39.27/5.49  --bmc1_pre_inst_state                   false
% 39.27/5.49  --bmc1_pre_inst_reach_state             false
% 39.27/5.49  --bmc1_out_unsat_core                   false
% 39.27/5.49  --bmc1_aig_witness_out                  false
% 39.27/5.49  --bmc1_verbose                          false
% 39.27/5.49  --bmc1_dump_clauses_tptp                false
% 39.27/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.27/5.49  --bmc1_dump_file                        -
% 39.27/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.27/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.27/5.49  --bmc1_ucm_extend_mode                  1
% 39.27/5.49  --bmc1_ucm_init_mode                    2
% 39.27/5.49  --bmc1_ucm_cone_mode                    none
% 39.27/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.27/5.49  --bmc1_ucm_relax_model                  4
% 39.27/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.27/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.27/5.49  --bmc1_ucm_layered_model                none
% 39.27/5.49  --bmc1_ucm_max_lemma_size               10
% 39.27/5.49  
% 39.27/5.49  ------ AIG Options
% 39.27/5.49  
% 39.27/5.49  --aig_mode                              false
% 39.27/5.49  
% 39.27/5.49  ------ Instantiation Options
% 39.27/5.49  
% 39.27/5.49  --instantiation_flag                    true
% 39.27/5.49  --inst_sos_flag                         false
% 39.27/5.49  --inst_sos_phase                        true
% 39.27/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.27/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.27/5.49  --inst_lit_sel_side                     num_symb
% 39.27/5.49  --inst_solver_per_active                1400
% 39.27/5.49  --inst_solver_calls_frac                1.
% 39.27/5.49  --inst_passive_queue_type               priority_queues
% 39.27/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.27/5.49  --inst_passive_queues_freq              [25;2]
% 39.27/5.49  --inst_dismatching                      true
% 39.27/5.49  --inst_eager_unprocessed_to_passive     true
% 39.27/5.49  --inst_prop_sim_given                   true
% 39.27/5.49  --inst_prop_sim_new                     false
% 39.27/5.49  --inst_subs_new                         false
% 39.27/5.49  --inst_eq_res_simp                      false
% 39.27/5.49  --inst_subs_given                       false
% 39.27/5.49  --inst_orphan_elimination               true
% 39.27/5.49  --inst_learning_loop_flag               true
% 39.27/5.49  --inst_learning_start                   3000
% 39.27/5.49  --inst_learning_factor                  2
% 39.27/5.49  --inst_start_prop_sim_after_learn       3
% 39.27/5.49  --inst_sel_renew                        solver
% 39.27/5.49  --inst_lit_activity_flag                true
% 39.27/5.49  --inst_restr_to_given                   false
% 39.27/5.49  --inst_activity_threshold               500
% 39.27/5.49  --inst_out_proof                        true
% 39.27/5.49  
% 39.27/5.49  ------ Resolution Options
% 39.27/5.49  
% 39.27/5.49  --resolution_flag                       true
% 39.27/5.49  --res_lit_sel                           adaptive
% 39.27/5.49  --res_lit_sel_side                      none
% 39.27/5.49  --res_ordering                          kbo
% 39.27/5.49  --res_to_prop_solver                    active
% 39.27/5.49  --res_prop_simpl_new                    false
% 39.27/5.49  --res_prop_simpl_given                  true
% 39.27/5.49  --res_passive_queue_type                priority_queues
% 39.27/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.27/5.49  --res_passive_queues_freq               [15;5]
% 39.27/5.49  --res_forward_subs                      full
% 39.27/5.49  --res_backward_subs                     full
% 39.27/5.49  --res_forward_subs_resolution           true
% 39.27/5.49  --res_backward_subs_resolution          true
% 39.27/5.49  --res_orphan_elimination                true
% 39.27/5.49  --res_time_limit                        2.
% 39.27/5.49  --res_out_proof                         true
% 39.27/5.49  
% 39.27/5.49  ------ Superposition Options
% 39.27/5.49  
% 39.27/5.49  --superposition_flag                    true
% 39.27/5.49  --sup_passive_queue_type                priority_queues
% 39.27/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.27/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.27/5.49  --demod_completeness_check              fast
% 39.27/5.49  --demod_use_ground                      true
% 39.27/5.49  --sup_to_prop_solver                    passive
% 39.27/5.49  --sup_prop_simpl_new                    true
% 39.27/5.49  --sup_prop_simpl_given                  true
% 39.27/5.49  --sup_fun_splitting                     false
% 39.27/5.49  --sup_smt_interval                      50000
% 39.27/5.49  
% 39.27/5.49  ------ Superposition Simplification Setup
% 39.27/5.49  
% 39.27/5.49  --sup_indices_passive                   []
% 39.27/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.27/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.27/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.27/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.27/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.27/5.49  --sup_full_bw                           [BwDemod]
% 39.27/5.49  --sup_immed_triv                        [TrivRules]
% 39.27/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.27/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.27/5.49  --sup_immed_bw_main                     []
% 39.27/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.27/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.27/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.27/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.27/5.49  
% 39.27/5.49  ------ Combination Options
% 39.27/5.49  
% 39.27/5.49  --comb_res_mult                         3
% 39.27/5.49  --comb_sup_mult                         2
% 39.27/5.49  --comb_inst_mult                        10
% 39.27/5.49  
% 39.27/5.49  ------ Debug Options
% 39.27/5.49  
% 39.27/5.49  --dbg_backtrace                         false
% 39.27/5.49  --dbg_dump_prop_clauses                 false
% 39.27/5.49  --dbg_dump_prop_clauses_file            -
% 39.27/5.49  --dbg_out_stat                          false
% 39.27/5.49  ------ Parsing...
% 39.27/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.27/5.49  
% 39.27/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 39.27/5.49  
% 39.27/5.49  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.27/5.49  
% 39.27/5.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.27/5.49  ------ Proving...
% 39.27/5.49  ------ Problem Properties 
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  clauses                                 23
% 39.27/5.49  conjectures                             2
% 39.27/5.49  EPR                                     1
% 39.27/5.49  Horn                                    18
% 39.27/5.49  unary                                   4
% 39.27/5.49  binary                                  2
% 39.27/5.49  lits                                    71
% 39.27/5.49  lits eq                                 5
% 39.27/5.49  fd_pure                                 0
% 39.27/5.49  fd_pseudo                               0
% 39.27/5.49  fd_cond                                 0
% 39.27/5.49  fd_pseudo_cond                          3
% 39.27/5.49  AC symbols                              0
% 39.27/5.49  
% 39.27/5.49  ------ Schedule dynamic 5 is on 
% 39.27/5.49  
% 39.27/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  ------ 
% 39.27/5.49  Current options:
% 39.27/5.49  ------ 
% 39.27/5.49  
% 39.27/5.49  ------ Input Options
% 39.27/5.49  
% 39.27/5.49  --out_options                           all
% 39.27/5.49  --tptp_safe_out                         true
% 39.27/5.49  --problem_path                          ""
% 39.27/5.49  --include_path                          ""
% 39.27/5.49  --clausifier                            res/vclausify_rel
% 39.27/5.49  --clausifier_options                    --mode clausify
% 39.27/5.49  --stdin                                 false
% 39.27/5.49  --stats_out                             all
% 39.27/5.49  
% 39.27/5.49  ------ General Options
% 39.27/5.49  
% 39.27/5.49  --fof                                   false
% 39.27/5.49  --time_out_real                         305.
% 39.27/5.49  --time_out_virtual                      -1.
% 39.27/5.49  --symbol_type_check                     false
% 39.27/5.49  --clausify_out                          false
% 39.27/5.49  --sig_cnt_out                           false
% 39.27/5.49  --trig_cnt_out                          false
% 39.27/5.49  --trig_cnt_out_tolerance                1.
% 39.27/5.49  --trig_cnt_out_sk_spl                   false
% 39.27/5.49  --abstr_cl_out                          false
% 39.27/5.49  
% 39.27/5.49  ------ Global Options
% 39.27/5.49  
% 39.27/5.49  --schedule                              default
% 39.27/5.49  --add_important_lit                     false
% 39.27/5.49  --prop_solver_per_cl                    1000
% 39.27/5.49  --min_unsat_core                        false
% 39.27/5.49  --soft_assumptions                      false
% 39.27/5.49  --soft_lemma_size                       3
% 39.27/5.49  --prop_impl_unit_size                   0
% 39.27/5.49  --prop_impl_unit                        []
% 39.27/5.49  --share_sel_clauses                     true
% 39.27/5.49  --reset_solvers                         false
% 39.27/5.49  --bc_imp_inh                            [conj_cone]
% 39.27/5.49  --conj_cone_tolerance                   3.
% 39.27/5.49  --extra_neg_conj                        none
% 39.27/5.49  --large_theory_mode                     true
% 39.27/5.49  --prolific_symb_bound                   200
% 39.27/5.49  --lt_threshold                          2000
% 39.27/5.49  --clause_weak_htbl                      true
% 39.27/5.49  --gc_record_bc_elim                     false
% 39.27/5.49  
% 39.27/5.49  ------ Preprocessing Options
% 39.27/5.49  
% 39.27/5.49  --preprocessing_flag                    true
% 39.27/5.49  --time_out_prep_mult                    0.1
% 39.27/5.49  --splitting_mode                        input
% 39.27/5.49  --splitting_grd                         true
% 39.27/5.49  --splitting_cvd                         false
% 39.27/5.49  --splitting_cvd_svl                     false
% 39.27/5.49  --splitting_nvd                         32
% 39.27/5.49  --sub_typing                            true
% 39.27/5.49  --prep_gs_sim                           true
% 39.27/5.49  --prep_unflatten                        true
% 39.27/5.49  --prep_res_sim                          true
% 39.27/5.49  --prep_upred                            true
% 39.27/5.49  --prep_sem_filter                       exhaustive
% 39.27/5.49  --prep_sem_filter_out                   false
% 39.27/5.49  --pred_elim                             true
% 39.27/5.49  --res_sim_input                         true
% 39.27/5.49  --eq_ax_congr_red                       true
% 39.27/5.49  --pure_diseq_elim                       true
% 39.27/5.49  --brand_transform                       false
% 39.27/5.49  --non_eq_to_eq                          false
% 39.27/5.49  --prep_def_merge                        true
% 39.27/5.49  --prep_def_merge_prop_impl              false
% 39.27/5.49  --prep_def_merge_mbd                    true
% 39.27/5.49  --prep_def_merge_tr_red                 false
% 39.27/5.49  --prep_def_merge_tr_cl                  false
% 39.27/5.49  --smt_preprocessing                     true
% 39.27/5.49  --smt_ac_axioms                         fast
% 39.27/5.49  --preprocessed_out                      false
% 39.27/5.49  --preprocessed_stats                    false
% 39.27/5.49  
% 39.27/5.49  ------ Abstraction refinement Options
% 39.27/5.49  
% 39.27/5.49  --abstr_ref                             []
% 39.27/5.49  --abstr_ref_prep                        false
% 39.27/5.49  --abstr_ref_until_sat                   false
% 39.27/5.49  --abstr_ref_sig_restrict                funpre
% 39.27/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.27/5.49  --abstr_ref_under                       []
% 39.27/5.49  
% 39.27/5.49  ------ SAT Options
% 39.27/5.49  
% 39.27/5.49  --sat_mode                              false
% 39.27/5.49  --sat_fm_restart_options                ""
% 39.27/5.49  --sat_gr_def                            false
% 39.27/5.49  --sat_epr_types                         true
% 39.27/5.49  --sat_non_cyclic_types                  false
% 39.27/5.49  --sat_finite_models                     false
% 39.27/5.49  --sat_fm_lemmas                         false
% 39.27/5.49  --sat_fm_prep                           false
% 39.27/5.49  --sat_fm_uc_incr                        true
% 39.27/5.49  --sat_out_model                         small
% 39.27/5.49  --sat_out_clauses                       false
% 39.27/5.49  
% 39.27/5.49  ------ QBF Options
% 39.27/5.49  
% 39.27/5.49  --qbf_mode                              false
% 39.27/5.49  --qbf_elim_univ                         false
% 39.27/5.49  --qbf_dom_inst                          none
% 39.27/5.49  --qbf_dom_pre_inst                      false
% 39.27/5.49  --qbf_sk_in                             false
% 39.27/5.49  --qbf_pred_elim                         true
% 39.27/5.49  --qbf_split                             512
% 39.27/5.49  
% 39.27/5.49  ------ BMC1 Options
% 39.27/5.49  
% 39.27/5.49  --bmc1_incremental                      false
% 39.27/5.49  --bmc1_axioms                           reachable_all
% 39.27/5.49  --bmc1_min_bound                        0
% 39.27/5.49  --bmc1_max_bound                        -1
% 39.27/5.49  --bmc1_max_bound_default                -1
% 39.27/5.49  --bmc1_symbol_reachability              true
% 39.27/5.49  --bmc1_property_lemmas                  false
% 39.27/5.49  --bmc1_k_induction                      false
% 39.27/5.49  --bmc1_non_equiv_states                 false
% 39.27/5.49  --bmc1_deadlock                         false
% 39.27/5.49  --bmc1_ucm                              false
% 39.27/5.49  --bmc1_add_unsat_core                   none
% 39.27/5.49  --bmc1_unsat_core_children              false
% 39.27/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.27/5.49  --bmc1_out_stat                         full
% 39.27/5.49  --bmc1_ground_init                      false
% 39.27/5.49  --bmc1_pre_inst_next_state              false
% 39.27/5.49  --bmc1_pre_inst_state                   false
% 39.27/5.49  --bmc1_pre_inst_reach_state             false
% 39.27/5.49  --bmc1_out_unsat_core                   false
% 39.27/5.49  --bmc1_aig_witness_out                  false
% 39.27/5.49  --bmc1_verbose                          false
% 39.27/5.49  --bmc1_dump_clauses_tptp                false
% 39.27/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.27/5.49  --bmc1_dump_file                        -
% 39.27/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.27/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.27/5.49  --bmc1_ucm_extend_mode                  1
% 39.27/5.49  --bmc1_ucm_init_mode                    2
% 39.27/5.49  --bmc1_ucm_cone_mode                    none
% 39.27/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.27/5.49  --bmc1_ucm_relax_model                  4
% 39.27/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.27/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.27/5.49  --bmc1_ucm_layered_model                none
% 39.27/5.49  --bmc1_ucm_max_lemma_size               10
% 39.27/5.49  
% 39.27/5.49  ------ AIG Options
% 39.27/5.49  
% 39.27/5.49  --aig_mode                              false
% 39.27/5.49  
% 39.27/5.49  ------ Instantiation Options
% 39.27/5.49  
% 39.27/5.49  --instantiation_flag                    true
% 39.27/5.49  --inst_sos_flag                         false
% 39.27/5.49  --inst_sos_phase                        true
% 39.27/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.27/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.27/5.49  --inst_lit_sel_side                     none
% 39.27/5.49  --inst_solver_per_active                1400
% 39.27/5.49  --inst_solver_calls_frac                1.
% 39.27/5.49  --inst_passive_queue_type               priority_queues
% 39.27/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.27/5.49  --inst_passive_queues_freq              [25;2]
% 39.27/5.49  --inst_dismatching                      true
% 39.27/5.49  --inst_eager_unprocessed_to_passive     true
% 39.27/5.49  --inst_prop_sim_given                   true
% 39.27/5.49  --inst_prop_sim_new                     false
% 39.27/5.49  --inst_subs_new                         false
% 39.27/5.49  --inst_eq_res_simp                      false
% 39.27/5.49  --inst_subs_given                       false
% 39.27/5.49  --inst_orphan_elimination               true
% 39.27/5.49  --inst_learning_loop_flag               true
% 39.27/5.49  --inst_learning_start                   3000
% 39.27/5.49  --inst_learning_factor                  2
% 39.27/5.49  --inst_start_prop_sim_after_learn       3
% 39.27/5.49  --inst_sel_renew                        solver
% 39.27/5.49  --inst_lit_activity_flag                true
% 39.27/5.49  --inst_restr_to_given                   false
% 39.27/5.49  --inst_activity_threshold               500
% 39.27/5.49  --inst_out_proof                        true
% 39.27/5.49  
% 39.27/5.49  ------ Resolution Options
% 39.27/5.49  
% 39.27/5.49  --resolution_flag                       false
% 39.27/5.49  --res_lit_sel                           adaptive
% 39.27/5.49  --res_lit_sel_side                      none
% 39.27/5.49  --res_ordering                          kbo
% 39.27/5.49  --res_to_prop_solver                    active
% 39.27/5.49  --res_prop_simpl_new                    false
% 39.27/5.49  --res_prop_simpl_given                  true
% 39.27/5.49  --res_passive_queue_type                priority_queues
% 39.27/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.27/5.49  --res_passive_queues_freq               [15;5]
% 39.27/5.49  --res_forward_subs                      full
% 39.27/5.49  --res_backward_subs                     full
% 39.27/5.49  --res_forward_subs_resolution           true
% 39.27/5.49  --res_backward_subs_resolution          true
% 39.27/5.49  --res_orphan_elimination                true
% 39.27/5.49  --res_time_limit                        2.
% 39.27/5.49  --res_out_proof                         true
% 39.27/5.49  
% 39.27/5.49  ------ Superposition Options
% 39.27/5.49  
% 39.27/5.49  --superposition_flag                    true
% 39.27/5.49  --sup_passive_queue_type                priority_queues
% 39.27/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.27/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.27/5.49  --demod_completeness_check              fast
% 39.27/5.49  --demod_use_ground                      true
% 39.27/5.49  --sup_to_prop_solver                    passive
% 39.27/5.49  --sup_prop_simpl_new                    true
% 39.27/5.49  --sup_prop_simpl_given                  true
% 39.27/5.49  --sup_fun_splitting                     false
% 39.27/5.49  --sup_smt_interval                      50000
% 39.27/5.49  
% 39.27/5.49  ------ Superposition Simplification Setup
% 39.27/5.49  
% 39.27/5.49  --sup_indices_passive                   []
% 39.27/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.27/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.27/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.27/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.27/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.27/5.49  --sup_full_bw                           [BwDemod]
% 39.27/5.49  --sup_immed_triv                        [TrivRules]
% 39.27/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.27/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.27/5.49  --sup_immed_bw_main                     []
% 39.27/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.27/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.27/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.27/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.27/5.49  
% 39.27/5.49  ------ Combination Options
% 39.27/5.49  
% 39.27/5.49  --comb_res_mult                         3
% 39.27/5.49  --comb_sup_mult                         2
% 39.27/5.49  --comb_inst_mult                        10
% 39.27/5.49  
% 39.27/5.49  ------ Debug Options
% 39.27/5.49  
% 39.27/5.49  --dbg_backtrace                         false
% 39.27/5.49  --dbg_dump_prop_clauses                 false
% 39.27/5.49  --dbg_dump_prop_clauses_file            -
% 39.27/5.49  --dbg_out_stat                          false
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  ------ Proving...
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  % SZS status Theorem for theBenchmark.p
% 39.27/5.49  
% 39.27/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.27/5.49  
% 39.27/5.49  fof(f6,axiom,(
% 39.27/5.49    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,X1,k3_lattices(X0,X3,X2)))))))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f25,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f6])).
% 39.27/5.49  
% 39.27/5.49  fof(f26,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f25])).
% 39.27/5.49  
% 39.27/5.49  fof(f68,plain,(
% 39.27/5.49    ( ! [X2,X0,X3,X1] : (r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f26])).
% 39.27/5.49  
% 39.27/5.49  fof(f12,conjecture,(
% 39.27/5.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f13,negated_conjecture,(
% 39.27/5.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 39.27/5.49    inference(negated_conjecture,[],[f12])).
% 39.27/5.49  
% 39.27/5.49  fof(f37,plain,(
% 39.27/5.49    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f13])).
% 39.27/5.49  
% 39.27/5.49  fof(f38,plain,(
% 39.27/5.49    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f37])).
% 39.27/5.49  
% 39.27/5.49  fof(f55,plain,(
% 39.27/5.49    ( ! [X0,X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) => ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,sK5)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,sK5)))) )),
% 39.27/5.49    introduced(choice_axiom,[])).
% 39.27/5.49  
% 39.27/5.49  fof(f54,plain,(
% 39.27/5.49    ( ! [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ~r3_lattices(X0,k3_lattices(X0,sK4,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,sK4,X2))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 39.27/5.49    introduced(choice_axiom,[])).
% 39.27/5.49  
% 39.27/5.49  fof(f53,plain,(
% 39.27/5.49    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ~r3_lattices(sK3,k3_lattices(sK3,X1,k16_lattice3(sK3,X2)),k16_lattice3(sK3,a_3_4_lattice3(sK3,X1,X2))) & m1_subset_1(X1,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 39.27/5.49    introduced(choice_axiom,[])).
% 39.27/5.49  
% 39.27/5.49  fof(f56,plain,(
% 39.27/5.49    (~r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 39.27/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f55,f54,f53])).
% 39.27/5.49  
% 39.27/5.49  fof(f85,plain,(
% 39.27/5.49    v10_lattices(sK3)),
% 39.27/5.49    inference(cnf_transformation,[],[f56])).
% 39.27/5.49  
% 39.27/5.49  fof(f84,plain,(
% 39.27/5.49    ~v2_struct_0(sK3)),
% 39.27/5.49    inference(cnf_transformation,[],[f56])).
% 39.27/5.49  
% 39.27/5.49  fof(f87,plain,(
% 39.27/5.49    l3_lattices(sK3)),
% 39.27/5.49    inference(cnf_transformation,[],[f56])).
% 39.27/5.49  
% 39.27/5.49  fof(f1,axiom,(
% 39.27/5.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f15,plain,(
% 39.27/5.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 39.27/5.49    inference(pure_predicate_removal,[],[f1])).
% 39.27/5.49  
% 39.27/5.49  fof(f16,plain,(
% 39.27/5.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 39.27/5.49    inference(ennf_transformation,[],[f15])).
% 39.27/5.49  
% 39.27/5.49  fof(f17,plain,(
% 39.27/5.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 39.27/5.49    inference(flattening,[],[f16])).
% 39.27/5.49  
% 39.27/5.49  fof(f62,plain,(
% 39.27/5.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f17])).
% 39.27/5.49  
% 39.27/5.49  fof(f4,axiom,(
% 39.27/5.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f21,plain,(
% 39.27/5.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f4])).
% 39.27/5.49  
% 39.27/5.49  fof(f22,plain,(
% 39.27/5.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f21])).
% 39.27/5.49  
% 39.27/5.49  fof(f39,plain,(
% 39.27/5.49    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(nnf_transformation,[],[f22])).
% 39.27/5.49  
% 39.27/5.49  fof(f65,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f39])).
% 39.27/5.49  
% 39.27/5.49  fof(f60,plain,(
% 39.27/5.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f17])).
% 39.27/5.49  
% 39.27/5.49  fof(f61,plain,(
% 39.27/5.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f17])).
% 39.27/5.49  
% 39.27/5.49  fof(f8,axiom,(
% 39.27/5.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f29,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f8])).
% 39.27/5.49  
% 39.27/5.49  fof(f30,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f29])).
% 39.27/5.49  
% 39.27/5.49  fof(f40,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(nnf_transformation,[],[f30])).
% 39.27/5.49  
% 39.27/5.49  fof(f41,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(rectify,[],[f40])).
% 39.27/5.49  
% 39.27/5.49  fof(f42,plain,(
% 39.27/5.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 39.27/5.49    introduced(choice_axiom,[])).
% 39.27/5.49  
% 39.27/5.49  fof(f43,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 39.27/5.49  
% 39.27/5.49  fof(f73,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f43])).
% 39.27/5.49  
% 39.27/5.49  fof(f71,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f43])).
% 39.27/5.49  
% 39.27/5.49  fof(f72,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f43])).
% 39.27/5.49  
% 39.27/5.49  fof(f10,axiom,(
% 39.27/5.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f33,plain,(
% 39.27/5.49    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 39.27/5.49    inference(ennf_transformation,[],[f10])).
% 39.27/5.49  
% 39.27/5.49  fof(f34,plain,(
% 39.27/5.49    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 39.27/5.49    inference(flattening,[],[f33])).
% 39.27/5.49  
% 39.27/5.49  fof(f44,plain,(
% 39.27/5.49    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 39.27/5.49    inference(nnf_transformation,[],[f34])).
% 39.27/5.49  
% 39.27/5.49  fof(f45,plain,(
% 39.27/5.49    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X5] : (r2_hidden(X5,X3) & k3_lattices(X1,X2,X5) = X0 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 39.27/5.49    inference(rectify,[],[f44])).
% 39.27/5.49  
% 39.27/5.49  fof(f46,plain,(
% 39.27/5.49    ! [X3,X2,X1,X0] : (? [X5] : (r2_hidden(X5,X3) & k3_lattices(X1,X2,X5) = X0 & m1_subset_1(X5,u1_struct_0(X1))) => (r2_hidden(sK1(X0,X1,X2,X3),X3) & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))))),
% 39.27/5.49    introduced(choice_axiom,[])).
% 39.27/5.49  
% 39.27/5.49  fof(f47,plain,(
% 39.27/5.49    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & ((r2_hidden(sK1(X0,X1,X2,X3),X3) & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 39.27/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 39.27/5.49  
% 39.27/5.49  fof(f76,plain,(
% 39.27/5.49    ( ! [X2,X0,X3,X1] : (k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f47])).
% 39.27/5.49  
% 39.27/5.49  fof(f86,plain,(
% 39.27/5.49    v4_lattice3(sK3)),
% 39.27/5.49    inference(cnf_transformation,[],[f56])).
% 39.27/5.49  
% 39.27/5.49  fof(f9,axiom,(
% 39.27/5.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f31,plain,(
% 39.27/5.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f9])).
% 39.27/5.49  
% 39.27/5.49  fof(f32,plain,(
% 39.27/5.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f31])).
% 39.27/5.49  
% 39.27/5.49  fof(f74,plain,(
% 39.27/5.49    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f32])).
% 39.27/5.49  
% 39.27/5.49  fof(f11,axiom,(
% 39.27/5.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f35,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f11])).
% 39.27/5.49  
% 39.27/5.49  fof(f36,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f35])).
% 39.27/5.49  
% 39.27/5.49  fof(f48,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(nnf_transformation,[],[f36])).
% 39.27/5.49  
% 39.27/5.49  fof(f49,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f48])).
% 39.27/5.49  
% 39.27/5.49  fof(f50,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(rectify,[],[f49])).
% 39.27/5.49  
% 39.27/5.49  fof(f51,plain,(
% 39.27/5.49    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK2(X0,X1,X2),X1) & r3_lattice3(X0,sK2(X0,X1,X2),X2) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 39.27/5.49    introduced(choice_axiom,[])).
% 39.27/5.49  
% 39.27/5.49  fof(f52,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK2(X0,X1,X2),X1) & r3_lattice3(X0,sK2(X0,X1,X2),X2) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 39.27/5.49  
% 39.27/5.49  fof(f80,plain,(
% 39.27/5.49    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f52])).
% 39.27/5.49  
% 39.27/5.49  fof(f91,plain,(
% 39.27/5.49    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(equality_resolution,[],[f80])).
% 39.27/5.49  
% 39.27/5.49  fof(f59,plain,(
% 39.27/5.49    ( ! [X0] : (v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f17])).
% 39.27/5.49  
% 39.27/5.49  fof(f7,axiom,(
% 39.27/5.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_lattices(X0,X2,X3) & r3_lattices(X0,X1,X3)) => r3_lattices(X0,k3_lattices(X0,X1,X2),X3))))))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f27,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_lattices(X0,k3_lattices(X0,X1,X2),X3) | (~r3_lattices(X0,X2,X3) | ~r3_lattices(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f7])).
% 39.27/5.49  
% 39.27/5.49  fof(f28,plain,(
% 39.27/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_lattices(X0,k3_lattices(X0,X1,X2),X3) | ~r3_lattices(X0,X2,X3) | ~r3_lattices(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f27])).
% 39.27/5.49  
% 39.27/5.49  fof(f69,plain,(
% 39.27/5.49    ( ! [X2,X0,X3,X1] : (r3_lattices(X0,k3_lattices(X0,X1,X2),X3) | ~r3_lattices(X0,X2,X3) | ~r3_lattices(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f28])).
% 39.27/5.49  
% 39.27/5.49  fof(f58,plain,(
% 39.27/5.49    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f17])).
% 39.27/5.49  
% 39.27/5.49  fof(f89,plain,(
% 39.27/5.49    ~r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)))),
% 39.27/5.49    inference(cnf_transformation,[],[f56])).
% 39.27/5.49  
% 39.27/5.49  fof(f88,plain,(
% 39.27/5.49    m1_subset_1(sK4,u1_struct_0(sK3))),
% 39.27/5.49    inference(cnf_transformation,[],[f56])).
% 39.27/5.49  
% 39.27/5.49  fof(f77,plain,(
% 39.27/5.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(X0,X1,X2,X3),X3) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f47])).
% 39.27/5.49  
% 39.27/5.49  fof(f66,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f39])).
% 39.27/5.49  
% 39.27/5.49  fof(f70,plain,(
% 39.27/5.49    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f43])).
% 39.27/5.49  
% 39.27/5.49  fof(f75,plain,(
% 39.27/5.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f47])).
% 39.27/5.49  
% 39.27/5.49  fof(f3,axiom,(
% 39.27/5.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f14,plain,(
% 39.27/5.49    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 39.27/5.49    inference(pure_predicate_removal,[],[f3])).
% 39.27/5.49  
% 39.27/5.49  fof(f20,plain,(
% 39.27/5.49    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 39.27/5.49    inference(ennf_transformation,[],[f14])).
% 39.27/5.49  
% 39.27/5.49  fof(f64,plain,(
% 39.27/5.49    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f20])).
% 39.27/5.49  
% 39.27/5.49  fof(f2,axiom,(
% 39.27/5.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f18,plain,(
% 39.27/5.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f2])).
% 39.27/5.49  
% 39.27/5.49  fof(f19,plain,(
% 39.27/5.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f18])).
% 39.27/5.49  
% 39.27/5.49  fof(f63,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f19])).
% 39.27/5.49  
% 39.27/5.49  fof(f5,axiom,(
% 39.27/5.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => r3_lattices(X0,X1,X1))),
% 39.27/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.27/5.49  
% 39.27/5.49  fof(f23,plain,(
% 39.27/5.49    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 39.27/5.49    inference(ennf_transformation,[],[f5])).
% 39.27/5.49  
% 39.27/5.49  fof(f24,plain,(
% 39.27/5.49    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 39.27/5.49    inference(flattening,[],[f23])).
% 39.27/5.49  
% 39.27/5.49  fof(f67,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f24])).
% 39.27/5.49  
% 39.27/5.49  fof(f79,plain,(
% 39.27/5.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(cnf_transformation,[],[f52])).
% 39.27/5.49  
% 39.27/5.49  fof(f92,plain,(
% 39.27/5.49    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 39.27/5.49    inference(equality_resolution,[],[f79])).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1383,plain,
% 39.27/5.49      ( ~ r3_lattices(X0_53,X0_54,X1_54)
% 39.27/5.49      | r3_lattices(X0_53,X2_54,X3_54)
% 39.27/5.49      | X2_54 != X0_54
% 39.27/5.49      | X3_54 != X1_54 ),
% 39.27/5.49      theory(equality) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_99295,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0_54,X1_54)
% 39.27/5.49      | r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != X1_54
% 39.27/5.49      | sK4 != X0_54 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1383]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_141597,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0_54,k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4))
% 39.27/5.49      | r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4)
% 39.27/5.49      | sK4 != X0_54 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_99295]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_141599,plain,
% 39.27/5.49      ( r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | ~ r3_lattices(sK3,sK4,k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4))
% 39.27/5.49      | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4)
% 39.27/5.49      | sK4 != sK4 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_141597]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1380,plain,
% 39.27/5.49      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 39.27/5.49      theory(equality) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_99747,plain,
% 39.27/5.49      ( X0_54 != X1_54
% 39.27/5.49      | X0_54 = k3_lattices(sK3,X2_54,X3_54)
% 39.27/5.49      | k3_lattices(sK3,X2_54,X3_54) != X1_54 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1380]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_104230,plain,
% 39.27/5.49      ( X0_54 != k3_lattices(sK3,X1_54,X2_54)
% 39.27/5.49      | X0_54 = k3_lattices(sK3,X2_54,X1_54)
% 39.27/5.49      | k3_lattices(sK3,X2_54,X1_54) != k3_lattices(sK3,X1_54,X2_54) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_99747]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_127276,plain,
% 39.27/5.49      ( sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4)
% 39.27/5.49      | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4) != k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_104230]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_11,plain,
% 39.27/5.49      ( ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f68]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_31,negated_conjecture,
% 39.27/5.49      ( v10_lattices(sK3) ),
% 39.27/5.49      inference(cnf_transformation,[],[f85]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1038,plain,
% 39.27/5.49      ( ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1039,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,k3_lattices(sK3,X2,X1))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_1038]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_32,negated_conjecture,
% 39.27/5.49      ( ~ v2_struct_0(sK3) ),
% 39.27/5.49      inference(cnf_transformation,[],[f84]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_29,negated_conjecture,
% 39.27/5.49      ( l3_lattices(sK3) ),
% 39.27/5.49      inference(cnf_transformation,[],[f87]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1043,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,k3_lattices(sK3,X2,X1))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_1039,c_32,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1044,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,k3_lattices(sK3,X2,X1))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_1043]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1359,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0_54,X1_54)
% 39.27/5.49      | r3_lattices(sK3,X0_54,k3_lattices(sK3,X2_54,X1_54))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_1044]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_118271,plain,
% 39.27/5.49      ( r3_lattices(sK3,sK4,k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4))
% 39.27/5.49      | ~ r3_lattices(sK3,sK4,sK4)
% 39.27/5.49      | ~ m1_subset_1(sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1359]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1378,plain,( X0_54 = X0_54 ),theory(equality) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_100957,plain,
% 39.27/5.49      ( sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1378]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_0,plain,
% 39.27/5.49      ( ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0)
% 39.27/5.49      | v9_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f62]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_9,plain,
% 39.27/5.49      ( r1_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v9_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f65]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_506,plain,
% 39.27/5.49      ( r1_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(resolution,[status(thm)],[c_0,c_9]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2,plain,
% 39.27/5.49      ( v6_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f60]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1,plain,
% 39.27/5.49      ( v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_510,plain,
% 39.27/5.49      ( r1_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_506,c_2,c_1]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_13,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f73]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_594,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X3,X4,X5)
% 39.27/5.49      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 39.27/5.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X3)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X3)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X3)
% 39.27/5.49      | X0 != X3
% 39.27/5.49      | X1 != X4
% 39.27/5.49      | sK0(X0,X1,X2) != X5 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_510,c_13]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_595,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_594]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_15,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f71]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_599,plain,
% 39.27/5.49      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 39.27/5.49      | r3_lattice3(X0,X1,X2)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_595,c_15]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_600,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_599]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_966,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_600,c_31]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_967,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_966]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_971,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_967,c_32,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1362,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0_54,X0_55)
% 39.27/5.49      | ~ r3_lattices(sK3,X0_54,sK0(sK3,X0_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_971]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_99051,plain,
% 39.27/5.49      ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ r3_lattices(sK3,sK4,sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1362]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2351,plain,
% 39.27/5.49      ( X0_54 != X1_54
% 39.27/5.49      | sK0(sK3,X2_54,X0_55) != X1_54
% 39.27/5.49      | sK0(sK3,X2_54,X0_55) = X0_54 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1380]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3315,plain,
% 39.27/5.49      ( X0_54 != sK0(sK3,X1_54,X0_55)
% 39.27/5.49      | sK0(sK3,X1_54,X0_55) = X0_54
% 39.27/5.49      | sK0(sK3,X1_54,X0_55) != sK0(sK3,X1_54,X0_55) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2351]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_67981,plain,
% 39.27/5.49      ( sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) != sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) = k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55))
% 39.27/5.49      | k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) != sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_3315]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_67982,plain,
% 39.27/5.49      ( sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_67981]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2572,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0_54,X1_54)
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),X2_54)
% 39.27/5.49      | X2_54 != X1_54
% 39.27/5.49      | k16_lattice3(sK3,sK5) != X0_54 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1383]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3303,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),X1_54)
% 39.27/5.49      | X1_54 != X0_54
% 39.27/5.49      | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2572]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_6925,plain,
% 39.27/5.49      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
% 39.27/5.49      | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,X1_54,X2_54))
% 39.27/5.49      | X0_54 != k3_lattices(sK3,X1_54,X2_54)
% 39.27/5.49      | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_3303]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_47105,plain,
% 39.27/5.49      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 39.27/5.49      | sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_6925]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_47125,plain,
% 39.27/5.49      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 39.27/5.49      | sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_47105]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2557,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,X1_54,X0_54))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1359]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_44576,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,X0_54,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2557]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_44588,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 39.27/5.49      | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_44576]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_14,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f72]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1173,plain,
% 39.27/5.49      ( r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1174,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r2_hidden(sK0(sK3,X0,X1),X1)
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_1173]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1178,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | r2_hidden(sK0(sK3,X0,X1),X1)
% 39.27/5.49      | r3_lattice3(sK3,X0,X1) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_1174,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1179,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r2_hidden(sK0(sK3,X0,X1),X1)
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_1178]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1354,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0_54,X0_55)
% 39.27/5.49      | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_1179]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1831,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0_54,X0_55) = iProver_top
% 39.27/5.49      | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55) = iProver_top
% 39.27/5.49      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1354]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_20,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ v4_lattice3(X1)
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X1)
% 39.27/5.49      | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 ),
% 39.27/5.49      inference(cnf_transformation,[],[f76]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_30,negated_conjecture,
% 39.27/5.49      ( v4_lattice3(sK3) ),
% 39.27/5.49      inference(cnf_transformation,[],[f86]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_723,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X1)
% 39.27/5.49      | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
% 39.27/5.49      | sK3 != X1 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_724,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3)
% 39.27/5.49      | ~ v10_lattices(sK3)
% 39.27/5.49      | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_723]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_728,plain,
% 39.27/5.49      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 39.27/5.49      | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_724,c_32,c_31,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_729,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_728]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1370,plain,
% 39.27/5.49      ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,X1_54,sK1(X0_54,sK3,X1_54,X0_55)) = X0_54 ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_729]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1813,plain,
% 39.27/5.49      ( k3_lattices(sK3,X0_54,sK1(X1_54,sK3,X0_54,X0_55)) = X1_54
% 39.27/5.49      | r2_hidden(X1_54,a_3_4_lattice3(sK3,X0_54,X0_55)) != iProver_top
% 39.27/5.49      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1370]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2722,plain,
% 39.27/5.49      ( k3_lattices(sK3,X0_54,sK1(sK0(sK3,X1_54,a_3_4_lattice3(sK3,X0_54,X0_55)),sK3,X0_54,X0_55)) = sK0(sK3,X1_54,a_3_4_lattice3(sK3,X0_54,X0_55))
% 39.27/5.49      | r3_lattice3(sK3,X1_54,a_3_4_lattice3(sK3,X0_54,X0_55)) = iProver_top
% 39.27/5.49      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(superposition,[status(thm)],[c_1831,c_1813]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_17,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f74]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1137,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1138,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_1137]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1142,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_1138,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_25,plain,
% 39.27/5.49      ( ~ r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 39.27/5.49      | ~ v4_lattice3(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f91]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_804,plain,
% 39.27/5.49      ( ~ r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_805,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3)
% 39.27/5.49      | ~ v10_lattices(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_804]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_809,plain,
% 39.27/5.49      ( ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 39.27/5.49      | ~ r3_lattice3(sK3,X0,X1) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_805,c_32,c_31,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_810,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_809]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1200,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(backward_subsumption_resolution,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_1142,c_810]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1353,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0_54,X0_55)
% 39.27/5.49      | r3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_1200]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1832,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0_54,X0_55) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55)) = iProver_top
% 39.27/5.49      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1353]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3,plain,
% 39.27/5.49      ( v5_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f59]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_12,plain,
% 39.27/5.49      ( ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X3,X2)
% 39.27/5.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ v4_lattices(X0)
% 39.27/5.49      | ~ v5_lattices(X0)
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v9_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f69]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_398,plain,
% 39.27/5.49      ( ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X3,X2)
% 39.27/5.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ v4_lattices(X0)
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0)
% 39.27/5.49      | ~ v9_lattices(X0) ),
% 39.27/5.49      inference(resolution,[status(thm)],[c_3,c_12]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_4,plain,
% 39.27/5.49      ( v4_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f58]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_402,plain,
% 39.27/5.49      ( ~ v10_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X3,X2)
% 39.27/5.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_398,c_4,c_2,c_1,c_0]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_403,plain,
% 39.27/5.49      ( ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X3,X2)
% 39.27/5.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_402]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1008,plain,
% 39.27/5.49      ( ~ r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ r3_lattices(X0,X3,X2)
% 39.27/5.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_403,c_31]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1009,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0,X1)
% 39.27/5.49      | ~ r3_lattices(sK3,X2,X1)
% 39.27/5.49      | r3_lattices(sK3,k3_lattices(sK3,X0,X2),X1)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_1008]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1013,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0,X1)
% 39.27/5.49      | ~ r3_lattices(sK3,X2,X1)
% 39.27/5.49      | r3_lattices(sK3,k3_lattices(sK3,X0,X2),X1)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_1009,c_32,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1014,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0,X1)
% 39.27/5.49      | ~ r3_lattices(sK3,X2,X1)
% 39.27/5.49      | r3_lattices(sK3,k3_lattices(sK3,X0,X2),X1)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_1013]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1360,plain,
% 39.27/5.49      ( ~ r3_lattices(sK3,X0_54,X1_54)
% 39.27/5.49      | ~ r3_lattices(sK3,X2_54,X1_54)
% 39.27/5.49      | r3_lattices(sK3,k3_lattices(sK3,X0_54,X2_54),X1_54)
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_1014]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1825,plain,
% 39.27/5.49      ( r3_lattices(sK3,X0_54,X1_54) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,X2_54,X1_54) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,k3_lattices(sK3,X0_54,X2_54),X1_54) = iProver_top
% 39.27/5.49      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(X2_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_27,negated_conjecture,
% 39.27/5.49      ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
% 39.27/5.49      inference(cnf_transformation,[],[f89]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1373,negated_conjecture,
% 39.27/5.49      ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_27]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1810,plain,
% 39.27/5.49      ( r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1373]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3400,plain,
% 39.27/5.49      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
% 39.27/5.49      | m1_subset_1(k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(superposition,[status(thm)],[c_1825,c_1810]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_28,negated_conjecture,
% 39.27/5.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(cnf_transformation,[],[f88]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_37,plain,
% 39.27/5.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1356,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_1142]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1447,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) = iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1356]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1449,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) = iProver_top ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1447]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2230,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1356]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2231,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)),u1_struct_0(sK3)) = iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_2230]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3481,plain,
% 39.27/5.49      ( r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_3400,c_37,c_1449,c_2231]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3482,plain,
% 39.27/5.49      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_3481]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3818,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
% 39.27/5.49      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(superposition,[status(thm)],[c_1832,c_3482]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_4199,plain,
% 39.27/5.49      ( r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top
% 39.27/5.49      | r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_3818,c_1449]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_4200,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
% 39.27/5.49      | r3_lattices(sK3,sK4,k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) != iProver_top ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_4199]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_4205,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
% 39.27/5.49      | r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
% 39.27/5.49      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(superposition,[status(thm)],[c_1832,c_4200]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_36328,plain,
% 39.27/5.49      ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
% 39.27/5.49      | r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_4205,c_37]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_36329,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
% 39.27/5.49      | r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_36328]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_36336,plain,
% 39.27/5.49      ( k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) != iProver_top
% 39.27/5.49      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(superposition,[status(thm)],[c_2722,c_36329]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_36359,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_36336]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_22989,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ r3_lattices(sK3,k16_lattice3(sK3,X0_55),sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1362]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_22993,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_22989]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2347,plain,
% 39.27/5.49      ( sK0(sK3,X0_54,X0_55) = sK0(sK3,X0_54,X0_55) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1378]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_22656,plain,
% 39.27/5.49      ( sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2347]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_22657,plain,
% 39.27/5.49      ( sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_22656]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_19,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 39.27/5.49      | r2_hidden(sK1(X0,X1,X2,X3),X3)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ v4_lattice3(X1)
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X1) ),
% 39.27/5.49      inference(cnf_transformation,[],[f77]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_744,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 39.27/5.49      | r2_hidden(sK1(X0,X1,X2,X3),X3)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X1)
% 39.27/5.49      | sK3 != X1 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_745,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 39.27/5.49      | r2_hidden(sK1(X0,sK3,X1,X2),X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3)
% 39.27/5.49      | ~ v10_lattices(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_744]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_749,plain,
% 39.27/5.49      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | r2_hidden(sK1(X0,sK3,X1,X2),X2)
% 39.27/5.49      | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_745,c_32,c_31,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_750,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 39.27/5.49      | r2_hidden(sK1(X0,sK3,X1,X2),X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_749]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1369,plain,
% 39.27/5.49      ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | r2_hidden(sK1(X0_54,sK3,X1_54,X0_55),X0_55)
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_750]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2389,plain,
% 39.27/5.49      ( r2_hidden(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X0_55)
% 39.27/5.49      | ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1369]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_19493,plain,
% 39.27/5.49      ( r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
% 39.27/5.49      | ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2389]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_19495,plain,
% 39.27/5.49      ( r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
% 39.27/5.49      | ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_19493]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_12841,plain,
% 39.27/5.49      ( sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_3315]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_12842,plain,
% 39.27/5.49      ( sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | k3_lattices(sK3,sK4,sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_12841]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_8,plain,
% 39.27/5.49      ( ~ r1_lattices(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v9_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_538,plain,
% 39.27/5.49      ( ~ r1_lattices(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(resolution,[status(thm)],[c_0,c_8]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_542,plain,
% 39.27/5.49      ( ~ r1_lattices(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,X2)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_538,c_8,c_2,c_1,c_0]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_16,plain,
% 39.27/5.49      ( ~ r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r1_lattices(X0,X1,X3)
% 39.27/5.49      | ~ r2_hidden(X3,X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f70]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_624,plain,
% 39.27/5.49      ( ~ r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X3,X4,X5)
% 39.27/5.49      | ~ r2_hidden(X6,X2)
% 39.27/5.49      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 39.27/5.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X6,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X3)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X3)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X3)
% 39.27/5.49      | X0 != X3
% 39.27/5.49      | X1 != X4
% 39.27/5.49      | X6 != X5 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_542,c_16]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_625,plain,
% 39.27/5.49      ( ~ r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,X3)
% 39.27/5.49      | ~ r2_hidden(X3,X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_624]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_939,plain,
% 39.27/5.49      ( ~ r3_lattice3(X0,X1,X2)
% 39.27/5.49      | r3_lattices(X0,X1,X3)
% 39.27/5.49      | ~ r2_hidden(X3,X2)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_625,c_31]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_940,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,X2)
% 39.27/5.49      | ~ r2_hidden(X2,X1)
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_939]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_944,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,X2)
% 39.27/5.49      | ~ r2_hidden(X2,X1)
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_940,c_32,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_945,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0,X1)
% 39.27/5.49      | r3_lattices(sK3,X0,X2)
% 39.27/5.49      | ~ r2_hidden(X2,X1)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_944]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1363,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,X0_54,X0_55)
% 39.27/5.49      | r3_lattices(sK3,X0_54,X1_54)
% 39.27/5.49      | ~ r2_hidden(X1_54,X0_55)
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_945]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2551,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),X0_55)
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_54)
% 39.27/5.49      | ~ r2_hidden(X0_54,X0_55)
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1363]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_3585,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),X0_55)
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55))
% 39.27/5.49      | ~ r2_hidden(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X0_55)
% 39.27/5.49      | ~ m1_subset_1(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2551]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_12678,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5)
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | ~ r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
% 39.27/5.49      | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_3585]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_12685,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5)
% 39.27/5.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 39.27/5.49      | ~ r2_hidden(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
% 39.27/5.49      | ~ m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_12678]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_21,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 39.27/5.49      | ~ v4_lattice3(X1)
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X1) ),
% 39.27/5.49      inference(cnf_transformation,[],[f75]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_702,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X1)
% 39.27/5.49      | sK3 != X1 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_703,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3)
% 39.27/5.49      | ~ v10_lattices(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_702]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_707,plain,
% 39.27/5.49      ( m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_703,c_32,c_31,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_708,plain,
% 39.27/5.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_707]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1371,plain,
% 39.27/5.49      ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | m1_subset_1(sK1(X0_54,sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_708]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2032,plain,
% 39.27/5.49      ( ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | m1_subset_1(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1371]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_7483,plain,
% 39.27/5.49      ( ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2032]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_7485,plain,
% 39.27/5.49      ( ~ r2_hidden(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | m1_subset_1(sK1(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_7483]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1812,plain,
% 39.27/5.49      ( r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) != iProver_top
% 39.27/5.49      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(sK1(X0_54,sK3,X1_54,X0_55),u1_struct_0(sK3)) = iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_7,plain,
% 39.27/5.49      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f64]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_6,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ l2_lattices(X1)
% 39.27/5.49      | ~ v4_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f63]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_367,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ v4_lattices(X1)
% 39.27/5.49      | ~ l3_lattices(X3)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | X1 != X3
% 39.27/5.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_7,c_6]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_368,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ v4_lattices(X1)
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_367]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_446,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ l3_lattices(X3)
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X3)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X3)
% 39.27/5.49      | X1 != X3
% 39.27/5.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_4,c_368]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_447,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | ~ v10_lattices(X1)
% 39.27/5.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_446]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1065,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.27/5.49      | ~ l3_lattices(X1)
% 39.27/5.49      | v2_struct_0(X1)
% 39.27/5.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 39.27/5.49      | sK3 != X1 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_447,c_31]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1066,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3)
% 39.27/5.49      | k3_lattices(sK3,X0,X1) = k3_lattices(sK3,X1,X0) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_1065]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1070,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,X0,X1) = k3_lattices(sK3,X1,X0) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_1066,c_32,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1071,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,X1,X0) = k3_lattices(sK3,X0,X1) ),
% 39.27/5.49      inference(renaming,[status(thm)],[c_1070]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1358,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,X1_54,X0_54) = k3_lattices(sK3,X0_54,X1_54) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_1071]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1827,plain,
% 39.27/5.49      ( k3_lattices(sK3,X0_54,X1_54) = k3_lattices(sK3,X1_54,X0_54)
% 39.27/5.49      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2516,plain,
% 39.27/5.49      ( k3_lattices(sK3,sK1(X0_54,sK3,X1_54,X0_55),X2_54) = k3_lattices(sK3,X2_54,sK1(X0_54,sK3,X1_54,X0_55))
% 39.27/5.49      | r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) != iProver_top
% 39.27/5.49      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(X2_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(superposition,[status(thm)],[c_1812,c_1827]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_5077,plain,
% 39.27/5.49      ( k3_lattices(sK3,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X2_54) = k3_lattices(sK3,X2_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55))
% 39.27/5.49      | r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) = iProver_top
% 39.27/5.49      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 39.27/5.49      | m1_subset_1(X2_54,u1_struct_0(sK3)) != iProver_top ),
% 39.27/5.49      inference(superposition,[status(thm)],[c_1831,c_2516]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_5119,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X2_54,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X2_54) = k3_lattices(sK3,X2_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) ),
% 39.27/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_5077]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_5121,plain,
% 39.27/5.49      ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK4) = k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_5119]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_4206,plain,
% 39.27/5.49      ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_4205]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2033,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1354]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_4149,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_55),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2033]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_4151,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | r2_hidden(sK0(sK3,k16_lattice3(sK3,sK5),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_4149]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2740,plain,
% 39.27/5.49      ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) = sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) ),
% 39.27/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_2722]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2742,plain,
% 39.27/5.49      ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 39.27/5.49      | k3_lattices(sK3,sK4,sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2740]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2039,plain,
% 39.27/5.49      ( r3_lattice3(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | r2_hidden(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2033]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_2035,plain,
% 39.27/5.49      ( ~ r2_hidden(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 39.27/5.49      | m1_subset_1(sK1(sK0(sK3,sK4,a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_2032]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1448,plain,
% 39.27/5.49      ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1356]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_10,plain,
% 39.27/5.49      ( r3_lattices(X0,X1,X1)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v9_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_477,plain,
% 39.27/5.49      ( r3_lattices(X0,X1,X1)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ v6_lattices(X0)
% 39.27/5.49      | ~ v8_lattices(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(resolution,[status(thm)],[c_0,c_10]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_481,plain,
% 39.27/5.49      ( r3_lattices(X0,X1,X1)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_477,c_10,c_2,c_1,c_0]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_987,plain,
% 39.27/5.49      ( r3_lattices(X0,X1,X1)
% 39.27/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_481,c_31]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_988,plain,
% 39.27/5.49      ( r3_lattices(sK3,X0,X0)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_987]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_992,plain,
% 39.27/5.49      ( r3_lattices(sK3,X0,X0)
% 39.27/5.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_988,c_32,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1361,plain,
% 39.27/5.49      ( r3_lattices(sK3,X0_54,X0_54)
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_992]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1374,plain,
% 39.27/5.49      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3)) | ~ sP0_iProver_split ),
% 39.27/5.49      inference(splitting,
% 39.27/5.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 39.27/5.49                [c_1361]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1435,plain,
% 39.27/5.49      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) | ~ sP0_iProver_split ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1374]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1375,plain,
% 39.27/5.49      ( r3_lattices(sK3,X0_54,X0_54)
% 39.27/5.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 39.27/5.49      | ~ sP1_iProver_split ),
% 39.27/5.49      inference(splitting,
% 39.27/5.49                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 39.27/5.49                [c_1361]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1432,plain,
% 39.27/5.49      ( r3_lattices(sK3,sK4,sK4)
% 39.27/5.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 39.27/5.49      | ~ sP1_iProver_split ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1375]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1376,plain,
% 39.27/5.49      ( sP1_iProver_split | sP0_iProver_split ),
% 39.27/5.49      inference(splitting,
% 39.27/5.49                [splitting(split),new_symbols(definition,[])],
% 39.27/5.49                [c_1361]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_26,plain,
% 39.27/5.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 39.27/5.49      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 39.27/5.49      | ~ v4_lattice3(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(cnf_transformation,[],[f92]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_191,plain,
% 39.27/5.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 39.27/5.49      | ~ v4_lattice3(X0)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_26,c_17]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_789,plain,
% 39.27/5.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 39.27/5.49      | ~ l3_lattices(X0)
% 39.27/5.49      | v2_struct_0(X0)
% 39.27/5.49      | ~ v10_lattices(X0)
% 39.27/5.49      | sK3 != X0 ),
% 39.27/5.49      inference(resolution_lifted,[status(thm)],[c_191,c_30]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_790,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0)
% 39.27/5.49      | ~ l3_lattices(sK3)
% 39.27/5.49      | v2_struct_0(sK3)
% 39.27/5.49      | ~ v10_lattices(sK3) ),
% 39.27/5.49      inference(unflattening,[status(thm)],[c_789]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_794,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0) ),
% 39.27/5.49      inference(global_propositional_subsumption,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_790,c_32,c_31,c_29]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1367,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),X0_55) ),
% 39.27/5.49      inference(subtyping,[status(esa)],[c_794]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1413,plain,
% 39.27/5.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1367]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1379,plain,( X0_55 = X0_55 ),theory(equality) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1397,plain,
% 39.27/5.49      ( sK5 = sK5 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1379]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1396,plain,
% 39.27/5.49      ( sK4 = sK4 ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1378]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1386,plain,
% 39.27/5.49      ( X0_55 != X1_55
% 39.27/5.49      | k16_lattice3(X0_53,X0_55) = k16_lattice3(X0_53,X1_55) ),
% 39.27/5.49      theory(equality) ).
% 39.27/5.49  
% 39.27/5.49  cnf(c_1393,plain,
% 39.27/5.49      ( sK5 != sK5 | k16_lattice3(sK3,sK5) = k16_lattice3(sK3,sK5) ),
% 39.27/5.49      inference(instantiation,[status(thm)],[c_1386]) ).
% 39.27/5.49  
% 39.27/5.49  cnf(contradiction,plain,
% 39.27/5.49      ( $false ),
% 39.27/5.49      inference(minisat,
% 39.27/5.49                [status(thm)],
% 39.27/5.49                [c_141599,c_127276,c_118271,c_100957,c_99051,c_67982,
% 39.27/5.49                 c_47125,c_44588,c_36359,c_22993,c_22657,c_19495,c_12842,
% 39.27/5.49                 c_12685,c_7485,c_5121,c_4206,c_4151,c_2742,c_2039,
% 39.27/5.49                 c_2035,c_1448,c_1435,c_1432,c_1376,c_1413,c_1397,c_1396,
% 39.27/5.49                 c_1393,c_28]) ).
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.27/5.49  
% 39.27/5.49  ------                               Statistics
% 39.27/5.49  
% 39.27/5.49  ------ General
% 39.27/5.49  
% 39.27/5.49  abstr_ref_over_cycles:                  0
% 39.27/5.49  abstr_ref_under_cycles:                 0
% 39.27/5.49  gc_basic_clause_elim:                   0
% 39.27/5.49  forced_gc_time:                         0
% 39.27/5.49  parsing_time:                           0.011
% 39.27/5.49  unif_index_cands_time:                  0.
% 39.27/5.49  unif_index_add_time:                    0.
% 39.27/5.49  orderings_time:                         0.
% 39.27/5.49  out_proof_time:                         0.023
% 39.27/5.49  total_time:                             4.706
% 39.27/5.49  num_of_symbols:                         59
% 39.27/5.49  num_of_terms:                           105342
% 39.27/5.49  
% 39.27/5.49  ------ Preprocessing
% 39.27/5.49  
% 39.27/5.49  num_of_splits:                          2
% 39.27/5.49  num_of_split_atoms:                     2
% 39.27/5.49  num_of_reused_defs:                     0
% 39.27/5.49  num_eq_ax_congr_red:                    46
% 39.27/5.49  num_of_sem_filtered_clauses:            3
% 39.27/5.49  num_of_subtypes:                        4
% 39.27/5.49  monotx_restored_types:                  0
% 39.27/5.49  sat_num_of_epr_types:                   0
% 39.27/5.49  sat_num_of_non_cyclic_types:            0
% 39.27/5.49  sat_guarded_non_collapsed_types:        1
% 39.27/5.49  num_pure_diseq_elim:                    0
% 39.27/5.49  simp_replaced_by:                       0
% 39.27/5.49  res_preprocessed:                       118
% 39.27/5.49  prep_upred:                             0
% 39.27/5.49  prep_unflattend:                        30
% 39.27/5.49  smt_new_axioms:                         0
% 39.27/5.49  pred_elim_cands:                        4
% 39.27/5.49  pred_elim:                              11
% 39.27/5.49  pred_elim_cl:                           11
% 39.27/5.49  pred_elim_cycles:                       13
% 39.27/5.49  merged_defs:                            0
% 39.27/5.49  merged_defs_ncl:                        0
% 39.27/5.49  bin_hyper_res:                          0
% 39.27/5.49  prep_cycles:                            4
% 39.27/5.49  pred_elim_time:                         0.018
% 39.27/5.49  splitting_time:                         0.
% 39.27/5.49  sem_filter_time:                        0.
% 39.27/5.49  monotx_time:                            0.
% 39.27/5.49  subtype_inf_time:                       0.
% 39.27/5.49  
% 39.27/5.49  ------ Problem properties
% 39.27/5.49  
% 39.27/5.49  clauses:                                23
% 39.27/5.49  conjectures:                            2
% 39.27/5.49  epr:                                    1
% 39.27/5.49  horn:                                   18
% 39.27/5.49  ground:                                 3
% 39.27/5.49  unary:                                  4
% 39.27/5.49  binary:                                 2
% 39.27/5.49  lits:                                   71
% 39.27/5.49  lits_eq:                                5
% 39.27/5.49  fd_pure:                                0
% 39.27/5.49  fd_pseudo:                              0
% 39.27/5.49  fd_cond:                                0
% 39.27/5.49  fd_pseudo_cond:                         3
% 39.27/5.49  ac_symbols:                             0
% 39.27/5.49  
% 39.27/5.49  ------ Propositional Solver
% 39.27/5.49  
% 39.27/5.49  prop_solver_calls:                      46
% 39.27/5.49  prop_fast_solver_calls:                 5227
% 39.27/5.49  smt_solver_calls:                       0
% 39.27/5.49  smt_fast_solver_calls:                  0
% 39.27/5.49  prop_num_of_clauses:                    32856
% 39.27/5.49  prop_preprocess_simplified:             65594
% 39.27/5.49  prop_fo_subsumed:                       165
% 39.27/5.49  prop_solver_time:                       0.
% 39.27/5.49  smt_solver_time:                        0.
% 39.27/5.49  smt_fast_solver_time:                   0.
% 39.27/5.49  prop_fast_solver_time:                  0.
% 39.27/5.49  prop_unsat_core_time:                   0.003
% 39.27/5.49  
% 39.27/5.49  ------ QBF
% 39.27/5.49  
% 39.27/5.49  qbf_q_res:                              0
% 39.27/5.49  qbf_num_tautologies:                    0
% 39.27/5.49  qbf_prep_cycles:                        0
% 39.27/5.49  
% 39.27/5.49  ------ BMC1
% 39.27/5.49  
% 39.27/5.49  bmc1_current_bound:                     -1
% 39.27/5.49  bmc1_last_solved_bound:                 -1
% 39.27/5.49  bmc1_unsat_core_size:                   -1
% 39.27/5.49  bmc1_unsat_core_parents_size:           -1
% 39.27/5.49  bmc1_merge_next_fun:                    0
% 39.27/5.49  bmc1_unsat_core_clauses_time:           0.
% 39.27/5.49  
% 39.27/5.49  ------ Instantiation
% 39.27/5.49  
% 39.27/5.49  inst_num_of_clauses:                    3083
% 39.27/5.49  inst_num_in_passive:                    1085
% 39.27/5.49  inst_num_in_active:                     3736
% 39.27/5.49  inst_num_in_unprocessed:                858
% 39.27/5.49  inst_num_of_loops:                      4289
% 39.27/5.49  inst_num_of_learning_restarts:          1
% 39.27/5.49  inst_num_moves_active_passive:          541
% 39.27/5.49  inst_lit_activity:                      0
% 39.27/5.49  inst_lit_activity_moves:                1
% 39.27/5.49  inst_num_tautologies:                   0
% 39.27/5.49  inst_num_prop_implied:                  0
% 39.27/5.49  inst_num_existing_simplified:           0
% 39.27/5.49  inst_num_eq_res_simplified:             0
% 39.27/5.49  inst_num_child_elim:                    0
% 39.27/5.49  inst_num_of_dismatching_blockings:      16349
% 39.27/5.49  inst_num_of_non_proper_insts:           17323
% 39.27/5.49  inst_num_of_duplicates:                 0
% 39.27/5.49  inst_inst_num_from_inst_to_res:         0
% 39.27/5.49  inst_dismatching_checking_time:         0.
% 39.27/5.49  
% 39.27/5.49  ------ Resolution
% 39.27/5.49  
% 39.27/5.49  res_num_of_clauses:                     31
% 39.27/5.49  res_num_in_passive:                     31
% 39.27/5.49  res_num_in_active:                      0
% 39.27/5.49  res_num_of_loops:                       122
% 39.27/5.49  res_forward_subset_subsumed:            1615
% 39.27/5.49  res_backward_subset_subsumed:           6
% 39.27/5.49  res_forward_subsumed:                   0
% 39.27/5.49  res_backward_subsumed:                  0
% 39.27/5.49  res_forward_subsumption_resolution:     1
% 39.27/5.49  res_backward_subsumption_resolution:    1
% 39.27/5.49  res_clause_to_clause_subsumption:       45944
% 39.27/5.49  res_orphan_elimination:                 0
% 39.27/5.49  res_tautology_del:                      1904
% 39.27/5.49  res_num_eq_res_simplified:              0
% 39.27/5.49  res_num_sel_changes:                    0
% 39.27/5.49  res_moves_from_active_to_pass:          0
% 39.27/5.49  
% 39.27/5.49  ------ Superposition
% 39.27/5.49  
% 39.27/5.49  sup_time_total:                         0.
% 39.27/5.49  sup_time_generating:                    0.
% 39.27/5.49  sup_time_sim_full:                      0.
% 39.27/5.49  sup_time_sim_immed:                     0.
% 39.27/5.49  
% 39.27/5.49  sup_num_of_clauses:                     3537
% 39.27/5.49  sup_num_in_active:                      855
% 39.27/5.49  sup_num_in_passive:                     2682
% 39.27/5.49  sup_num_of_loops:                       856
% 39.27/5.49  sup_fw_superposition:                   2547
% 39.27/5.49  sup_bw_superposition:                   1168
% 39.27/5.49  sup_immediate_simplified:               121
% 39.27/5.49  sup_given_eliminated:                   0
% 39.27/5.49  comparisons_done:                       0
% 39.27/5.49  comparisons_avoided:                    1075
% 39.27/5.49  
% 39.27/5.49  ------ Simplifications
% 39.27/5.49  
% 39.27/5.49  
% 39.27/5.49  sim_fw_subset_subsumed:                 13
% 39.27/5.49  sim_bw_subset_subsumed:                 25
% 39.27/5.49  sim_fw_subsumed:                        46
% 39.27/5.49  sim_bw_subsumed:                        0
% 39.27/5.49  sim_fw_subsumption_res:                 14
% 39.27/5.49  sim_bw_subsumption_res:                 0
% 39.27/5.49  sim_tautology_del:                      1
% 39.27/5.49  sim_eq_tautology_del:                   29
% 39.27/5.49  sim_eq_res_simp:                        1
% 39.27/5.49  sim_fw_demodulated:                     22
% 39.27/5.49  sim_bw_demodulated:                     0
% 39.27/5.49  sim_light_normalised:                   43
% 39.27/5.49  sim_joinable_taut:                      0
% 39.27/5.49  sim_joinable_simp:                      0
% 39.27/5.49  sim_ac_normalised:                      0
% 39.27/5.49  sim_smt_subsumption:                    0
% 39.27/5.49  
%------------------------------------------------------------------------------
