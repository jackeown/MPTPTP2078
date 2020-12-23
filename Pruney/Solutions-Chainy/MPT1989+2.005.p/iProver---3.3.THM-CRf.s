%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:36 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 764 expanded)
%              Number of clauses        :  136 ( 204 expanded)
%              Number of leaves         :   23 ( 189 expanded)
%              Depth                    :   22
%              Number of atoms          : 1446 (5448 expanded)
%              Number of equality atoms :  164 ( 190 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_waybel_7(sK7,X0)
        & v5_waybel_6(sK7,X0)
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK6)
          & v5_waybel_6(X1,sK6)
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l1_orders_2(sK6)
      & v2_lattice3(sK6)
      & v1_lattice3(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ~ v4_waybel_7(sK7,sK6)
    & v5_waybel_6(sK7,sK6)
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l1_orders_2(sK6)
    & v2_lattice3(sK6)
    & v1_lattice3(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f46,f69,f68])).

fof(f119,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f118,plain,(
    v2_lattice3(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
        & r2_lattice3(X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f116,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f120,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f70])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,(
    v5_waybel_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r1_orders_2(X0,X3,X1)
                        & ~ r1_orders_2(X0,X2,X1)
                        & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | r1_orders_2(X0,X2,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & ~ r1_orders_2(X0,X2,X1)
          & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1),X1)
        & ~ r1_orders_2(X0,X2,X1)
        & r1_orders_2(X0,k11_lattice3(X0,X2,sK4(X0,X1)),X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X3,X1)
              & ~ r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_orders_2(X0,X3,X1)
            & ~ r1_orders_2(X0,sK3(X0,X1),X1)
            & r1_orders_2(X0,k11_lattice3(X0,sK3(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ( ~ r1_orders_2(X0,sK4(X0,X1),X1)
                & ~ r1_orders_2(X0,sK3(X0,X1),X1)
                & r1_orders_2(X0,k11_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f60,f62,f61])).

fof(f100,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X5,X1)
      | r1_orders_2(X0,X4,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK5(X0,X1)) = X1
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK5(X0,X1),X0)
        & v12_waybel_0(sK5(X0,X1),X0)
        & v1_waybel_0(sK5(X0,X1),X0)
        & ~ v1_xboole_0(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK5(X0,X1)) = X1
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK5(X0,X1),X0)
                & v12_waybel_0(sK5(X0,X1),X0)
                & v1_waybel_0(sK5(X0,X1),X0)
                & ~ v1_xboole_0(sK5(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f128,plain,(
    ! [X2,X0] :
      ( v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f115,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f117,plain,(
    v1_lattice3(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,(
    ~ v4_waybel_7(sK7,sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_46,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2976,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_46])).

cnf(c_2977,plain,
    ( r2_lattice3(sK6,X0,X1)
    | r2_hidden(sK0(sK6,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_2976])).

cnf(c_5096,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | r2_hidden(sK0(sK6,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2977])).

cnf(c_28,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1663,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_28,c_1])).

cnf(c_47,negated_conjecture,
    ( v2_lattice3(sK6) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2660,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1663,c_47])).

cnf(c_2661,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_2660])).

cnf(c_2665,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
    | r1_orders_2(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2661,c_46])).

cnf(c_2666,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_2665])).

cnf(c_5108,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2666])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1751,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_1752,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(unflattening,[status(thm)],[c_1751])).

cnf(c_2780,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1752,c_47])).

cnf(c_2781,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_2780])).

cnf(c_2785,plain,
    ( m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2781,c_46])).

cnf(c_2786,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(renaming,[status(thm)],[c_2785])).

cnf(c_5447,plain,
    ( ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_0,c_2786])).

cnf(c_6221,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
    | r1_orders_2(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2666,c_46,c_2661,c_5447])).

cnf(c_6222,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_6221])).

cnf(c_6223,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6222])).

cnf(c_11389,plain,
    ( r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5108,c_6223])).

cnf(c_11390,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11389])).

cnf(c_11393,plain,
    ( r1_orders_2(sK6,sK0(sK6,k5_waybel_0(sK6,X0),X1),X0) = iProver_top
    | r2_lattice3(sK6,k5_waybel_0(sK6,X0),X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5096,c_11390])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2991,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_46])).

cnf(c_2992,plain,
    ( ~ r1_orders_2(sK6,sK0(sK6,X0,X1),X1)
    | r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_2991])).

cnf(c_5095,plain,
    ( r1_orders_2(sK6,sK0(sK6,X0,X1),X1) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2992])).

cnf(c_11584,plain,
    ( r2_lattice3(sK6,k5_waybel_0(sK6,X0),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11393,c_5095])).

cnf(c_19,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_49,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2276,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_49])).

cnf(c_2277,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | r2_lattice3(sK6,X0,sK2(sK6,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_2276])).

cnf(c_2281,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_lattice3(sK6,X0,sK2(sK6,X1,X0))
    | ~ r2_lattice3(sK6,X0,X1)
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2277,c_46])).

cnf(c_2282,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | r2_lattice3(sK6,X0,sK2(sK6,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(renaming,[status(thm)],[c_2281])).

cnf(c_5114,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_lattice3(sK6,X0,sK2(sK6,X1,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_20,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2252,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_49])).

cnf(c_2253,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_2252])).

cnf(c_2257,plain,
    ( m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,X0,X1)
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2253,c_46])).

cnf(c_2258,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(renaming,[status(thm)],[c_2257])).

cnf(c_5115,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_5127,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_5,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2940,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_46])).

cnf(c_2941,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_2940])).

cnf(c_5098,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2941])).

cnf(c_5569,plain,
    ( r1_orders_2(sK6,sK7,X0) = iProver_top
    | r2_lattice3(sK6,X1,X0) != iProver_top
    | r2_hidden(sK7,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5127,c_5098])).

cnf(c_14872,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r1_orders_2(sK6,sK7,sK2(sK6,X1,X0)) = iProver_top
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_lattice3(sK6,X2,sK2(sK6,X1,X0)) != iProver_top
    | r2_hidden(sK7,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5115,c_5569])).

cnf(c_15034,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r1_orders_2(sK6,sK7,sK2(sK6,X1,X0)) = iProver_top
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5114,c_14872])).

cnf(c_18,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2300,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X2) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_49])).

cnf(c_2301,plain,
    ( ~ r1_orders_2(sK6,X0,sK2(sK6,X0,X1))
    | ~ r2_lattice3(sK6,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | k1_yellow_0(sK6,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_2300])).

cnf(c_2305,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,X1,X0)
    | ~ r1_orders_2(sK6,X0,sK2(sK6,X0,X1))
    | k1_yellow_0(sK6,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2301,c_46])).

cnf(c_2306,plain,
    ( ~ r1_orders_2(sK6,X0,sK2(sK6,X0,X1))
    | ~ r2_lattice3(sK6,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k1_yellow_0(sK6,X1) = X0 ),
    inference(renaming,[status(thm)],[c_2305])).

cnf(c_5113,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r1_orders_2(sK6,X1,sK2(sK6,X1,X0)) != iProver_top
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2306])).

cnf(c_15285,plain,
    ( k1_yellow_0(sK6,X0) = sK7
    | r2_lattice3(sK6,X0,sK7) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15034,c_5113])).

cnf(c_58,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_15745,plain,
    ( r2_hidden(sK7,X0) != iProver_top
    | r2_lattice3(sK6,X0,sK7) != iProver_top
    | k1_yellow_0(sK6,X0) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15285,c_58])).

cnf(c_15746,plain,
    ( k1_yellow_0(sK6,X0) = sK7
    | r2_lattice3(sK6,X0,sK7) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15745])).

cnf(c_15751,plain,
    ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK7)) = sK7
    | r2_hidden(sK7,k5_waybel_0(sK6,sK7)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11584,c_15746])).

cnf(c_44,negated_conjecture,
    ( v5_waybel_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_59,plain,
    ( v5_waybel_6(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3006,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_46])).

cnf(c_3007,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k11_lattice3(sK6,X1,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_3006])).

cnf(c_13,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_341,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_1])).

cnf(c_342,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_2190,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_342,c_49])).

cnf(c_2191,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k11_lattice3(sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6) ),
    inference(unflattening,[status(thm)],[c_2190])).

cnf(c_2193,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k11_lattice3(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2191,c_47,c_46])).

cnf(c_2194,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k11_lattice3(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_2193])).

cnf(c_3044,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3007,c_2194])).

cnf(c_5360,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,X0),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3044])).

cnf(c_5521,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5360])).

cnf(c_5522,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5521])).

cnf(c_34,plain,
    ( r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
    | ~ v5_waybel_6(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1571,plain,
    ( r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
    | ~ v5_waybel_6(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_34,c_1])).

cnf(c_2747,plain,
    ( r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
    | ~ v5_waybel_6(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1571,c_47])).

cnf(c_2748,plain,
    ( r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,X2,X1)
    | ~ r1_orders_2(sK6,k11_lattice3(sK6,X2,X0),X1)
    | ~ v5_waybel_6(X1,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_2747])).

cnf(c_2752,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v5_waybel_6(X1,sK6)
    | ~ r1_orders_2(sK6,k11_lattice3(sK6,X2,X0),X1)
    | r1_orders_2(sK6,X2,X1)
    | r1_orders_2(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2748,c_46])).

cnf(c_2753,plain,
    ( r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,X2,X1)
    | ~ r1_orders_2(sK6,k11_lattice3(sK6,X2,X0),X1)
    | ~ v5_waybel_6(X1,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_2752])).

cnf(c_5898,plain,
    ( ~ r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7)
    | r1_orders_2(sK6,sK7,sK7)
    | ~ v5_waybel_6(sK7,sK6)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2753])).

cnf(c_5899,plain,
    ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7) != iProver_top
    | r1_orders_2(sK6,sK7,sK7) = iProver_top
    | v5_waybel_6(sK7,sK6) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5898])).

cnf(c_27,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1686,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_27,c_1])).

cnf(c_2636,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1686,c_47])).

cnf(c_2637,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | r2_hidden(X0,k5_waybel_0(sK6,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_2636])).

cnf(c_2641,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k5_waybel_0(sK6,X1))
    | ~ r1_orders_2(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2637,c_46])).

cnf(c_2642,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | r2_hidden(X0,k5_waybel_0(sK6,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_2641])).

cnf(c_6848,plain,
    ( ~ r1_orders_2(sK6,sK7,sK7)
    | r2_hidden(sK7,k5_waybel_0(sK6,sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2642])).

cnf(c_6849,plain,
    ( r1_orders_2(sK6,sK7,sK7) != iProver_top
    | r2_hidden(sK7,k5_waybel_0(sK6,sK7)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6848])).

cnf(c_15867,plain,
    ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15751,c_58,c_59,c_5522,c_5899,c_6849])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_51,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1492,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_51])).

cnf(c_1493,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v1_xboole_0(k5_waybel_0(sK6,X0))
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1492])).

cnf(c_181,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1497,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v1_xboole_0(k5_waybel_0(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_47,c_46,c_181])).

cnf(c_24,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_35,plain,
    ( ~ v1_waybel_7(X0,X1)
    | v4_waybel_7(k1_yellow_0(X1,X0),X1)
    | ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_624,plain,
    ( ~ v1_waybel_7(X0,X1)
    | v4_waybel_7(k1_yellow_0(X1,X0),X1)
    | ~ v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v2_struct_0(X3)
    | X1 != X3
    | k5_waybel_0(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_625,plain,
    ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
    | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_yellow_0(X0,k5_waybel_0(X0,X1)),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | v1_xboole_0(k5_waybel_0(X0,X1))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_25,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_629,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v1_xboole_0(k5_waybel_0(X0,X1))
    | ~ v1_lattice3(X0)
    | ~ m1_subset_1(k1_yellow_0(X0,k5_waybel_0(X0,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_25,c_1])).

cnf(c_630,plain,
    ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_yellow_0(X0,k5_waybel_0(X0,X1)),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | v1_xboole_0(k5_waybel_0(X0,X1))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_629])).

cnf(c_14,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_659,plain,
    ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_lattice3(X0)
    | v1_xboole_0(k5_waybel_0(X0,X1))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_630,c_14])).

cnf(c_50,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1309,plain,
    ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_lattice3(X0)
    | v1_xboole_0(k5_waybel_0(X0,X1))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_659,c_50])).

cnf(c_1310,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_lattice3(sK6)
    | v1_xboole_0(k5_waybel_0(sK6,X0))
    | ~ v3_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6) ),
    inference(unflattening,[status(thm)],[c_1309])).

cnf(c_48,negated_conjecture,
    ( v1_lattice3(sK6) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1314,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
    | ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | v1_xboole_0(k5_waybel_0(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1310,c_51,c_49,c_48,c_47,c_46])).

cnf(c_1315,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v1_xboole_0(k5_waybel_0(sK6,X0)) ),
    inference(renaming,[status(thm)],[c_1314])).

cnf(c_1512,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1497,c_1315])).

cnf(c_2872,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2786,c_1512])).

cnf(c_5100,plain,
    ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6) != iProver_top
    | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2872])).

cnf(c_15869,plain,
    ( v1_waybel_7(k5_waybel_0(sK6,sK7),sK6) != iProver_top
    | v4_waybel_7(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15867,c_5100])).

cnf(c_42,plain,
    ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | ~ v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1336,plain,
    ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | ~ v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_50])).

cnf(c_1337,plain,
    ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | ~ v5_waybel_6(X0,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v1_lattice3(sK6)
    | ~ v3_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6) ),
    inference(unflattening,[status(thm)],[c_1336])).

cnf(c_1341,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v5_waybel_6(X0,sK6)
    | v1_waybel_7(k5_waybel_0(sK6,X0),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1337,c_51,c_49,c_48,c_47,c_46])).

cnf(c_1342,plain,
    ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | ~ v5_waybel_6(X0,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1341])).

cnf(c_3284,plain,
    ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | sK6 != sK6
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_1342])).

cnf(c_3285,plain,
    ( v1_waybel_7(k5_waybel_0(sK6,sK7),sK6)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_3284])).

cnf(c_3286,plain,
    ( v1_waybel_7(k5_waybel_0(sK6,sK7),sK6) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3285])).

cnf(c_43,negated_conjecture,
    ( ~ v4_waybel_7(sK7,sK6) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_60,plain,
    ( v4_waybel_7(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15869,c_3286,c_60,c_58])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.97/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/0.98  
% 3.97/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.98  
% 3.97/0.98  ------  iProver source info
% 3.97/0.98  
% 3.97/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.98  git: non_committed_changes: false
% 3.97/0.98  git: last_make_outside_of_git: false
% 3.97/0.98  
% 3.97/0.98  ------ 
% 3.97/0.98  ------ Parsing...
% 3.97/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/0.98  ------ Proving...
% 3.97/0.98  ------ Problem Properties 
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  clauses                                 40
% 3.97/0.98  conjectures                             3
% 3.97/0.98  EPR                                     2
% 3.97/0.98  Horn                                    27
% 3.97/0.98  unary                                   4
% 3.97/0.98  binary                                  2
% 3.97/0.98  lits                                    144
% 3.97/0.98  lits eq                                 8
% 3.97/0.98  fd_pure                                 0
% 3.97/0.98  fd_pseudo                               0
% 3.97/0.98  fd_cond                                 0
% 3.97/0.98  fd_pseudo_cond                          7
% 3.97/0.98  AC symbols                              0
% 3.97/0.98  
% 3.97/0.98  ------ Input Options Time Limit: Unbounded
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  ------ 
% 3.97/0.98  Current options:
% 3.97/0.98  ------ 
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  ------ Proving...
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  % SZS status Theorem for theBenchmark.p
% 3.97/0.98  
% 3.97/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.98  
% 3.97/0.98  fof(f3,axiom,(
% 3.97/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f22,plain,(
% 3.97/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(ennf_transformation,[],[f3])).
% 3.97/0.98  
% 3.97/0.98  fof(f23,plain,(
% 3.97/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(flattening,[],[f22])).
% 3.97/0.98  
% 3.97/0.98  fof(f47,plain,(
% 3.97/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(nnf_transformation,[],[f23])).
% 3.97/0.98  
% 3.97/0.98  fof(f48,plain,(
% 3.97/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(rectify,[],[f47])).
% 3.97/0.98  
% 3.97/0.98  fof(f49,plain,(
% 3.97/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f50,plain,(
% 3.97/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 3.97/0.98  
% 3.97/0.98  fof(f75,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f50])).
% 3.97/0.98  
% 3.97/0.98  fof(f15,conjecture,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f16,negated_conjecture,(
% 3.97/0.98    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 3.97/0.98    inference(negated_conjecture,[],[f15])).
% 3.97/0.98  
% 3.97/0.98  fof(f45,plain,(
% 3.97/0.98    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f16])).
% 3.97/0.98  
% 3.97/0.98  fof(f46,plain,(
% 3.97/0.98    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 3.97/0.98    inference(flattening,[],[f45])).
% 3.97/0.98  
% 3.97/0.98  fof(f69,plain,(
% 3.97/0.98    ( ! [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_waybel_7(sK7,X0) & v5_waybel_6(sK7,X0) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f68,plain,(
% 3.97/0.98    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK6) & v5_waybel_6(X1,sK6) & m1_subset_1(X1,u1_struct_0(sK6))) & l1_orders_2(sK6) & v2_lattice3(sK6) & v1_lattice3(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6))),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f70,plain,(
% 3.97/0.98    (~v4_waybel_7(sK7,sK6) & v5_waybel_6(sK7,sK6) & m1_subset_1(sK7,u1_struct_0(sK6))) & l1_orders_2(sK6) & v2_lattice3(sK6) & v1_lattice3(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6)),
% 3.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f46,f69,f68])).
% 3.97/0.98  
% 3.97/0.98  fof(f119,plain,(
% 3.97/0.98    l1_orders_2(sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f11,axiom,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f37,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f11])).
% 3.97/0.98  
% 3.97/0.98  fof(f38,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(flattening,[],[f37])).
% 3.97/0.98  
% 3.97/0.98  fof(f58,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(nnf_transformation,[],[f38])).
% 3.97/0.98  
% 3.97/0.98  fof(f98,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f58])).
% 3.97/0.98  
% 3.97/0.98  fof(f2,axiom,(
% 3.97/0.98    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f20,plain,(
% 3.97/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(ennf_transformation,[],[f2])).
% 3.97/0.98  
% 3.97/0.98  fof(f21,plain,(
% 3.97/0.98    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(flattening,[],[f20])).
% 3.97/0.98  
% 3.97/0.98  fof(f72,plain,(
% 3.97/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f21])).
% 3.97/0.98  
% 3.97/0.98  fof(f118,plain,(
% 3.97/0.98    v2_lattice3(sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f1,axiom,(
% 3.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f18,plain,(
% 3.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.97/0.98    inference(ennf_transformation,[],[f1])).
% 3.97/0.98  
% 3.97/0.98  fof(f19,plain,(
% 3.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.97/0.98    inference(flattening,[],[f18])).
% 3.97/0.98  
% 3.97/0.98  fof(f71,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f19])).
% 3.97/0.98  
% 3.97/0.98  fof(f8,axiom,(
% 3.97/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f31,plain,(
% 3.97/0.98    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f8])).
% 3.97/0.98  
% 3.97/0.98  fof(f32,plain,(
% 3.97/0.98    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(flattening,[],[f31])).
% 3.97/0.98  
% 3.97/0.98  fof(f94,plain,(
% 3.97/0.98    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f32])).
% 3.97/0.98  
% 3.97/0.98  fof(f76,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f50])).
% 3.97/0.98  
% 3.97/0.98  fof(f7,axiom,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f17,plain,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 3.97/0.98    inference(rectify,[],[f7])).
% 3.97/0.98  
% 3.97/0.98  fof(f29,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f17])).
% 3.97/0.98  
% 3.97/0.98  fof(f30,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.97/0.98    inference(flattening,[],[f29])).
% 3.97/0.98  
% 3.97/0.98  fof(f56,plain,(
% 3.97/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK2(X0,X1,X2)) & r2_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f57,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK2(X0,X1,X2)) & r2_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f56])).
% 3.97/0.98  
% 3.97/0.98  fof(f89,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | r2_lattice3(X0,X2,sK2(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f57])).
% 3.97/0.98  
% 3.97/0.98  fof(f116,plain,(
% 3.97/0.98    v5_orders_2(sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f88,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f57])).
% 3.97/0.98  
% 3.97/0.98  fof(f120,plain,(
% 3.97/0.98    m1_subset_1(sK7,u1_struct_0(sK6))),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f73,plain,(
% 3.97/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f50])).
% 3.97/0.98  
% 3.97/0.98  fof(f90,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK2(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f57])).
% 3.97/0.98  
% 3.97/0.98  fof(f121,plain,(
% 3.97/0.98    v5_waybel_6(sK7,sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f4,axiom,(
% 3.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f24,plain,(
% 3.97/0.98    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f4])).
% 3.97/0.98  
% 3.97/0.98  fof(f25,plain,(
% 3.97/0.98    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(flattening,[],[f24])).
% 3.97/0.98  
% 3.97/0.98  fof(f77,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f25])).
% 3.97/0.98  
% 3.97/0.98  fof(f5,axiom,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f26,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f5])).
% 3.97/0.98  
% 3.97/0.98  fof(f27,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(flattening,[],[f26])).
% 3.97/0.98  
% 3.97/0.98  fof(f51,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(nnf_transformation,[],[f27])).
% 3.97/0.98  
% 3.97/0.98  fof(f52,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(flattening,[],[f51])).
% 3.97/0.98  
% 3.97/0.98  fof(f53,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(rectify,[],[f52])).
% 3.97/0.98  
% 3.97/0.98  fof(f54,plain,(
% 3.97/0.98    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f55,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 3.97/0.98  
% 3.97/0.98  fof(f78,plain,(
% 3.97/0.98    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f55])).
% 3.97/0.98  
% 3.97/0.98  fof(f125,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(equality_resolution,[],[f78])).
% 3.97/0.98  
% 3.97/0.98  fof(f12,axiom,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)))))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f39,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : ((v5_waybel_6(X1,X0) <=> ! [X2] : (! [X3] : ((r1_orders_2(X0,X3,X1) | r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f12])).
% 3.97/0.98  
% 3.97/0.98  fof(f40,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : ((v5_waybel_6(X1,X0) <=> ! [X2] : (! [X3] : (r1_orders_2(X0,X3,X1) | r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(flattening,[],[f39])).
% 3.97/0.98  
% 3.97/0.98  fof(f59,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (((v5_waybel_6(X1,X0) | ? [X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r1_orders_2(X0,X3,X1) | r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v5_waybel_6(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(nnf_transformation,[],[f40])).
% 3.97/0.98  
% 3.97/0.98  fof(f60,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (((v5_waybel_6(X1,X0) | ? [X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_orders_2(X0,X5,X1) | r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_waybel_6(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(rectify,[],[f59])).
% 3.97/0.98  
% 3.97/0.98  fof(f62,plain,(
% 3.97/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1),X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,sK4(X0,X1)),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))) )),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f61,plain,(
% 3.97/0.98    ! [X1,X0] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,sK3(X0,X1),X1) & r1_orders_2(X0,k11_lattice3(X0,sK3(X0,X1),X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f63,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (((v5_waybel_6(X1,X0) | ((~r1_orders_2(X0,sK4(X0,X1),X1) & ~r1_orders_2(X0,sK3(X0,X1),X1) & r1_orders_2(X0,k11_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_orders_2(X0,X5,X1) | r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_waybel_6(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f60,f62,f61])).
% 3.97/0.98  
% 3.97/0.98  fof(f100,plain,(
% 3.97/0.98    ( ! [X4,X0,X5,X1] : (r1_orders_2(X0,X5,X1) | r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f63])).
% 3.97/0.98  
% 3.97/0.98  fof(f99,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f58])).
% 3.97/0.98  
% 3.97/0.98  fof(f10,axiom,(
% 3.97/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f35,plain,(
% 3.97/0.98    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f10])).
% 3.97/0.98  
% 3.97/0.98  fof(f36,plain,(
% 3.97/0.98    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(flattening,[],[f35])).
% 3.97/0.98  
% 3.97/0.98  fof(f96,plain,(
% 3.97/0.98    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f36])).
% 3.97/0.98  
% 3.97/0.98  fof(f114,plain,(
% 3.97/0.98    v3_orders_2(sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f9,axiom,(
% 3.97/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f33,plain,(
% 3.97/0.98    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f9])).
% 3.97/0.98  
% 3.97/0.98  fof(f34,plain,(
% 3.97/0.98    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 3.97/0.98    inference(flattening,[],[f33])).
% 3.97/0.98  
% 3.97/0.98  fof(f95,plain,(
% 3.97/0.98    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f34])).
% 3.97/0.98  
% 3.97/0.98  fof(f13,axiom,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f41,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f13])).
% 3.97/0.98  
% 3.97/0.98  fof(f42,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.97/0.98    inference(flattening,[],[f41])).
% 3.97/0.98  
% 3.97/0.98  fof(f64,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.97/0.98    inference(nnf_transformation,[],[f42])).
% 3.97/0.98  
% 3.97/0.98  fof(f65,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.97/0.98    inference(rectify,[],[f64])).
% 3.97/0.98  
% 3.97/0.98  fof(f66,plain,(
% 3.97/0.98    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK5(X0,X1)) = X1 & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK5(X0,X1),X0) & v12_waybel_0(sK5(X0,X1),X0) & v1_waybel_0(sK5(X0,X1),X0) & ~v1_xboole_0(sK5(X0,X1))))),
% 3.97/0.98    introduced(choice_axiom,[])).
% 3.97/0.98  
% 3.97/0.98  fof(f67,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK5(X0,X1)) = X1 & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK5(X0,X1),X0) & v12_waybel_0(sK5(X0,X1),X0) & v1_waybel_0(sK5(X0,X1),X0) & ~v1_xboole_0(sK5(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).
% 3.97/0.98  
% 3.97/0.98  fof(f112,plain,(
% 3.97/0.98    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f67])).
% 3.97/0.98  
% 3.97/0.98  fof(f128,plain,(
% 3.97/0.98    ( ! [X2,X0] : (v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.97/0.98    inference(equality_resolution,[],[f112])).
% 3.97/0.98  
% 3.97/0.98  fof(f97,plain,(
% 3.97/0.98    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f36])).
% 3.97/0.98  
% 3.97/0.98  fof(f6,axiom,(
% 3.97/0.98    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f28,plain,(
% 3.97/0.98    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.97/0.98    inference(ennf_transformation,[],[f6])).
% 3.97/0.98  
% 3.97/0.98  fof(f85,plain,(
% 3.97/0.98    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f28])).
% 3.97/0.98  
% 3.97/0.98  fof(f115,plain,(
% 3.97/0.98    v4_orders_2(sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f117,plain,(
% 3.97/0.98    v1_lattice3(sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  fof(f14,axiom,(
% 3.97/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 3.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.98  
% 3.97/0.98  fof(f43,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 3.97/0.98    inference(ennf_transformation,[],[f14])).
% 3.97/0.98  
% 3.97/0.98  fof(f44,plain,(
% 3.97/0.98    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.97/0.98    inference(flattening,[],[f43])).
% 3.97/0.98  
% 3.97/0.98  fof(f113,plain,(
% 3.97/0.98    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.97/0.98    inference(cnf_transformation,[],[f44])).
% 3.97/0.98  
% 3.97/0.98  fof(f122,plain,(
% 3.97/0.98    ~v4_waybel_7(sK7,sK6)),
% 3.97/0.98    inference(cnf_transformation,[],[f70])).
% 3.97/0.98  
% 3.97/0.98  cnf(c_3,plain,
% 3.97/0.98      ( r2_lattice3(X0,X1,X2)
% 3.97/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_46,negated_conjecture,
% 3.97/0.98      ( l1_orders_2(sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2976,plain,
% 3.97/0.98      ( r2_lattice3(X0,X1,X2)
% 3.97/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2977,plain,
% 3.97/0.98      ( r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | r2_hidden(sK0(sK6,X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2976]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5096,plain,
% 3.97/0.98      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.97/0.98      | r2_hidden(sK0(sK6,X0,X1),X0) = iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2977]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_28,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | v2_struct_0(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1,plain,
% 3.97/0.98      ( ~ l1_orders_2(X0) | ~ v2_lattice3(X0) | ~ v2_struct_0(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1663,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0) ),
% 3.97/0.98      inference(resolution,[status(thm)],[c_28,c_1]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_47,negated_conjecture,
% 3.97/0.98      ( v2_lattice3(sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f118]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2660,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_1663,c_47]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2661,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ l1_orders_2(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2660]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2665,plain,
% 3.97/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | r1_orders_2(sK6,X0,X1) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2661,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2666,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2665]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5108,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.97/0.98      | r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
% 3.97/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2666]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_0,plain,
% 3.97/0.98      ( ~ r2_hidden(X0,X1)
% 3.97/0.98      | m1_subset_1(X0,X2)
% 3.97/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.97/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_23,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | v2_struct_0(X1) ),
% 3.97/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1751,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/0.98      | ~ l1_orders_2(X2)
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | ~ v2_lattice3(X2)
% 3.97/0.98      | X1 != X2 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1752,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | ~ v2_lattice3(X1) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_1751]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2780,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | sK6 != X1 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_1752,c_47]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2781,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.97/0.98      | ~ l1_orders_2(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2780]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2785,plain,
% 3.97/0.98      ( m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2781,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2786,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2785]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5447,plain,
% 3.97/0.98      ( ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(resolution,[status(thm)],[c_0,c_2786]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_6221,plain,
% 3.97/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | r1_orders_2(sK6,X0,X1) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2666,c_46,c_2661,c_5447]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_6222,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | ~ r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_6221]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_6223,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.97/0.98      | r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_6222]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_11389,plain,
% 3.97/0.98      ( r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
% 3.97/0.98      | r1_orders_2(sK6,X0,X1) = iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_5108,c_6223]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_11390,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.97/0.98      | r2_hidden(X0,k5_waybel_0(sK6,X1)) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_11389]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_11393,plain,
% 3.97/0.98      ( r1_orders_2(sK6,sK0(sK6,k5_waybel_0(sK6,X0),X1),X0) = iProver_top
% 3.97/0.98      | r2_lattice3(sK6,k5_waybel_0(sK6,X0),X1) = iProver_top
% 3.97/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_5096,c_11390]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2,plain,
% 3.97/0.98      ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 3.97/0.98      | r2_lattice3(X0,X1,X2)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2991,plain,
% 3.97/0.98      ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 3.97/0.98      | r2_lattice3(X0,X1,X2)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2992,plain,
% 3.97/0.98      ( ~ r1_orders_2(sK6,sK0(sK6,X0,X1),X1)
% 3.97/0.98      | r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2991]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5095,plain,
% 3.97/0.98      ( r1_orders_2(sK6,sK0(sK6,X0,X1),X1) != iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X0,X1) = iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2992]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_11584,plain,
% 3.97/0.98      ( r2_lattice3(sK6,k5_waybel_0(sK6,X0),X0) = iProver_top
% 3.97/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_11393,c_5095]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_19,plain,
% 3.97/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.97/0.98      | r2_lattice3(X0,X1,sK2(X0,X2,X1))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | k1_yellow_0(X0,X1) = X2 ),
% 3.97/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_49,negated_conjecture,
% 3.97/0.98      ( v5_orders_2(sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2276,plain,
% 3.97/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.97/0.98      | r2_lattice3(X0,X1,sK2(X0,X2,X1))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | k1_yellow_0(X0,X1) = X2
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_49]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2277,plain,
% 3.97/0.98      ( ~ r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | r2_lattice3(sK6,X0,sK2(sK6,X1,X0))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ l1_orders_2(sK6)
% 3.97/0.98      | k1_yellow_0(sK6,X0) = X1 ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2276]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2281,plain,
% 3.97/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | r2_lattice3(sK6,X0,sK2(sK6,X1,X0))
% 3.97/0.98      | ~ r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | k1_yellow_0(sK6,X0) = X1 ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2277,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2282,plain,
% 3.97/0.98      ( ~ r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | r2_lattice3(sK6,X0,sK2(sK6,X1,X0))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | k1_yellow_0(sK6,X0) = X1 ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2281]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5114,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,X0) = X1
% 3.97/0.98      | r2_lattice3(sK6,X0,X1) != iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X0,sK2(sK6,X1,X0)) = iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2282]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_20,plain,
% 3.97/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | k1_yellow_0(X0,X1) = X2 ),
% 3.97/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2252,plain,
% 3.97/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | k1_yellow_0(X0,X1) = X2
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_49]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2253,plain,
% 3.97/0.98      ( ~ r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
% 3.97/0.98      | ~ l1_orders_2(sK6)
% 3.97/0.98      | k1_yellow_0(sK6,X0) = X1 ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2252]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2257,plain,
% 3.97/0.98      ( m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | k1_yellow_0(sK6,X0) = X1 ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2253,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2258,plain,
% 3.97/0.98      ( ~ r2_lattice3(sK6,X0,X1)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
% 3.97/0.98      | k1_yellow_0(sK6,X0) = X1 ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2257]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5115,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,X0) = X1
% 3.97/0.98      | r2_lattice3(sK6,X0,X1) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.97/0.98      | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2258]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_45,negated_conjecture,
% 3.97/0.98      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5127,plain,
% 3.97/0.98      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | ~ r2_lattice3(X0,X3,X2)
% 3.97/0.98      | ~ r2_hidden(X1,X3)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2940,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | ~ r2_lattice3(X0,X3,X2)
% 3.97/0.98      | ~ r2_hidden(X1,X3)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2941,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | ~ r2_lattice3(sK6,X2,X1)
% 3.97/0.98      | ~ r2_hidden(X0,X2)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2940]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5098,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.97/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.97/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2941]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5569,plain,
% 3.97/0.98      ( r1_orders_2(sK6,sK7,X0) = iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X1,X0) != iProver_top
% 3.97/0.98      | r2_hidden(sK7,X1) != iProver_top
% 3.97/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_5127,c_5098]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_14872,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,X0) = X1
% 3.97/0.98      | r1_orders_2(sK6,sK7,sK2(sK6,X1,X0)) = iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X0,X1) != iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X2,sK2(sK6,X1,X0)) != iProver_top
% 3.97/0.98      | r2_hidden(sK7,X2) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_5115,c_5569]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_15034,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,X0) = X1
% 3.97/0.98      | r1_orders_2(sK6,sK7,sK2(sK6,X1,X0)) = iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X0,X1) != iProver_top
% 3.97/0.98      | r2_hidden(sK7,X0) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_5114,c_14872]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_18,plain,
% 3.97/0.98      ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
% 3.97/0.98      | ~ r2_lattice3(X0,X2,X1)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | k1_yellow_0(X0,X2) = X1 ),
% 3.97/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2300,plain,
% 3.97/0.98      ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
% 3.97/0.98      | ~ r2_lattice3(X0,X2,X1)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | k1_yellow_0(X0,X2) = X1
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_49]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2301,plain,
% 3.97/0.98      ( ~ r1_orders_2(sK6,X0,sK2(sK6,X0,X1))
% 3.97/0.98      | ~ r2_lattice3(sK6,X1,X0)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ l1_orders_2(sK6)
% 3.97/0.98      | k1_yellow_0(sK6,X1) = X0 ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2300]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2305,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ r2_lattice3(sK6,X1,X0)
% 3.97/0.98      | ~ r1_orders_2(sK6,X0,sK2(sK6,X0,X1))
% 3.97/0.98      | k1_yellow_0(sK6,X1) = X0 ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2301,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2306,plain,
% 3.97/0.98      ( ~ r1_orders_2(sK6,X0,sK2(sK6,X0,X1))
% 3.97/0.98      | ~ r2_lattice3(sK6,X1,X0)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | k1_yellow_0(sK6,X1) = X0 ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2305]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5113,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,X0) = X1
% 3.97/0.98      | r1_orders_2(sK6,X1,sK2(sK6,X1,X0)) != iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X0,X1) != iProver_top
% 3.97/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2306]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_15285,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,X0) = sK7
% 3.97/0.98      | r2_lattice3(sK6,X0,sK7) != iProver_top
% 3.97/0.98      | r2_hidden(sK7,X0) != iProver_top
% 3.97/0.98      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_15034,c_5113]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_58,plain,
% 3.97/0.98      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_15745,plain,
% 3.97/0.98      ( r2_hidden(sK7,X0) != iProver_top
% 3.97/0.98      | r2_lattice3(sK6,X0,sK7) != iProver_top
% 3.97/0.98      | k1_yellow_0(sK6,X0) = sK7 ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_15285,c_58]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_15746,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,X0) = sK7
% 3.97/0.98      | r2_lattice3(sK6,X0,sK7) != iProver_top
% 3.97/0.98      | r2_hidden(sK7,X0) != iProver_top ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_15745]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_15751,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK7)) = sK7
% 3.97/0.98      | r2_hidden(sK7,k5_waybel_0(sK6,sK7)) != iProver_top
% 3.97/0.98      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_11584,c_15746]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_44,negated_conjecture,
% 3.97/0.98      ( v5_waybel_6(sK7,sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_59,plain,
% 3.97/0.98      ( v5_waybel_6(sK7,sK6) = iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_6,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.97/0.98      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.97/0.98      | ~ l1_orders_2(X1) ),
% 3.97/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_3006,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.97/0.98      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.97/0.98      | sK6 != X1 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_3007,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | m1_subset_1(k11_lattice3(sK6,X1,X0),u1_struct_0(sK6)) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_3006]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_13,plain,
% 3.97/0.98      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0)
% 3.97/0.98      | v2_struct_0(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f125]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_341,plain,
% 3.97/0.98      ( ~ v2_lattice3(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_13,c_1]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_342,plain,
% 3.97/0.98      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_341]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2190,plain,
% 3.97/0.98      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0)
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_342,c_49]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2191,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(k11_lattice3(sK6,X0,X1),u1_struct_0(sK6))
% 3.97/0.98      | ~ l1_orders_2(sK6)
% 3.97/0.98      | ~ v2_lattice3(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2190]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2193,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(k11_lattice3(sK6,X0,X1),u1_struct_0(sK6)) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2191,c_47,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2194,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(k11_lattice3(sK6,X0,X1),u1_struct_0(sK6)) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2193]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_3044,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(backward_subsumption_resolution,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_3007,c_2194]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5360,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,X0),sK7)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(instantiation,[status(thm)],[c_3044]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5521,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7)
% 3.97/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(instantiation,[status(thm)],[c_5360]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5522,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7) = iProver_top
% 3.97/0.98      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_5521]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_34,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | r1_orders_2(X0,X3,X2)
% 3.97/0.98      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
% 3.97/0.98      | ~ v5_waybel_6(X2,X0)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | v2_struct_0(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1571,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | r1_orders_2(X0,X3,X2)
% 3.97/0.98      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
% 3.97/0.98      | ~ v5_waybel_6(X2,X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0) ),
% 3.97/0.98      inference(resolution,[status(thm)],[c_34,c_1]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2747,plain,
% 3.97/0.98      ( r1_orders_2(X0,X1,X2)
% 3.97/0.98      | r1_orders_2(X0,X3,X2)
% 3.97/0.98      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
% 3.97/0.98      | ~ v5_waybel_6(X2,X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_1571,c_47]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2748,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | r1_orders_2(sK6,X2,X1)
% 3.97/0.98      | ~ r1_orders_2(sK6,k11_lattice3(sK6,X2,X0),X1)
% 3.97/0.98      | ~ v5_waybel_6(X1,sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ l1_orders_2(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2747]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2752,plain,
% 3.97/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ v5_waybel_6(X1,sK6)
% 3.97/0.98      | ~ r1_orders_2(sK6,k11_lattice3(sK6,X2,X0),X1)
% 3.97/0.98      | r1_orders_2(sK6,X2,X1)
% 3.97/0.98      | r1_orders_2(sK6,X0,X1) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2748,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2753,plain,
% 3.97/0.98      ( r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | r1_orders_2(sK6,X2,X1)
% 3.97/0.98      | ~ r1_orders_2(sK6,k11_lattice3(sK6,X2,X0),X1)
% 3.97/0.98      | ~ v5_waybel_6(X1,sK6)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2752]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5898,plain,
% 3.97/0.98      ( ~ r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7)
% 3.97/0.98      | r1_orders_2(sK6,sK7,sK7)
% 3.97/0.98      | ~ v5_waybel_6(sK7,sK6)
% 3.97/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(instantiation,[status(thm)],[c_2753]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5899,plain,
% 3.97/0.98      ( r1_orders_2(sK6,k11_lattice3(sK6,sK7,sK7),sK7) != iProver_top
% 3.97/0.98      | r1_orders_2(sK6,sK7,sK7) = iProver_top
% 3.97/0.98      | v5_waybel_6(sK7,sK6) != iProver_top
% 3.97/0.98      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_5898]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_27,plain,
% 3.97/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.97/0.98      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | v2_struct_0(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1686,plain,
% 3.97/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.97/0.98      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0) ),
% 3.97/0.98      inference(resolution,[status(thm)],[c_27,c_1]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2636,plain,
% 3.97/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.97/0.98      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_1686,c_47]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2637,plain,
% 3.97/0.98      ( ~ r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ l1_orders_2(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_2636]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2641,plain,
% 3.97/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | ~ r1_orders_2(sK6,X0,X1) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2637,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2642,plain,
% 3.97/0.98      ( ~ r1_orders_2(sK6,X0,X1)
% 3.97/0.98      | r2_hidden(X0,k5_waybel_0(sK6,X1))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_2641]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_6848,plain,
% 3.97/0.98      ( ~ r1_orders_2(sK6,sK7,sK7)
% 3.97/0.98      | r2_hidden(sK7,k5_waybel_0(sK6,sK7))
% 3.97/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(instantiation,[status(thm)],[c_2642]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_6849,plain,
% 3.97/0.98      ( r1_orders_2(sK6,sK7,sK7) != iProver_top
% 3.97/0.98      | r2_hidden(sK7,k5_waybel_0(sK6,sK7)) = iProver_top
% 3.97/0.98      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_6848]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_15867,plain,
% 3.97/0.98      ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK7)) = sK7 ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_15751,c_58,c_59,c_5522,c_5899,c_6849]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_26,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 3.97/0.98      | ~ v3_orders_2(X1)
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | v2_struct_0(X1) ),
% 3.97/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_51,negated_conjecture,
% 3.97/0.98      ( v3_orders_2(sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1492,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.98      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | v2_struct_0(X1)
% 3.97/0.98      | sK6 != X1 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_51]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1493,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ v1_xboole_0(k5_waybel_0(sK6,X0))
% 3.97/0.98      | ~ l1_orders_2(sK6)
% 3.97/0.98      | v2_struct_0(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_1492]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_181,plain,
% 3.97/0.98      ( ~ l1_orders_2(sK6) | ~ v2_lattice3(sK6) | ~ v2_struct_0(sK6) ),
% 3.97/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1497,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ v1_xboole_0(k5_waybel_0(sK6,X0)) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_1493,c_47,c_46,c_181]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_24,plain,
% 3.97/0.98      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ v4_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | v2_struct_0(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_35,plain,
% 3.97/0.98      ( ~ v1_waybel_7(X0,X1)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(X1,X0),X1)
% 3.97/0.98      | ~ v1_waybel_0(X0,X1)
% 3.97/0.98      | ~ v12_waybel_0(X0,X1)
% 3.97/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/0.98      | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
% 3.97/0.98      | ~ v1_lattice3(X1)
% 3.97/0.98      | v1_xboole_0(X0)
% 3.97/0.98      | ~ v3_orders_2(X1)
% 3.97/0.98      | ~ v4_orders_2(X1)
% 3.97/0.98      | ~ v5_orders_2(X1)
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | ~ v2_lattice3(X1) ),
% 3.97/0.98      inference(cnf_transformation,[],[f128]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_624,plain,
% 3.97/0.98      ( ~ v1_waybel_7(X0,X1)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(X1,X0),X1)
% 3.97/0.98      | ~ v1_waybel_0(X0,X1)
% 3.97/0.98      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 3.97/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/0.98      | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
% 3.97/0.98      | ~ v1_lattice3(X1)
% 3.97/0.98      | v1_xboole_0(X0)
% 3.97/0.98      | ~ v3_orders_2(X1)
% 3.97/0.98      | ~ v4_orders_2(X3)
% 3.97/0.98      | ~ v4_orders_2(X1)
% 3.97/0.98      | ~ v5_orders_2(X1)
% 3.97/0.98      | ~ l1_orders_2(X3)
% 3.97/0.98      | ~ l1_orders_2(X1)
% 3.97/0.98      | ~ v2_lattice3(X1)
% 3.97/0.98      | v2_struct_0(X3)
% 3.97/0.98      | X1 != X3
% 3.97/0.98      | k5_waybel_0(X3,X2) != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_625,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
% 3.97/0.98      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/0.98      | ~ m1_subset_1(k1_yellow_0(X0,k5_waybel_0(X0,X1)),u1_struct_0(X0))
% 3.97/0.98      | ~ v1_lattice3(X0)
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(X0,X1))
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | ~ v4_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0)
% 3.97/0.98      | v2_struct_0(X0) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_624]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_25,plain,
% 3.97/0.98      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | v2_struct_0(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_629,plain,
% 3.97/0.98      ( ~ v2_lattice3(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ v4_orders_2(X0)
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(X0,X1))
% 3.97/0.98      | ~ v1_lattice3(X0)
% 3.97/0.98      | ~ m1_subset_1(k1_yellow_0(X0,k5_waybel_0(X0,X1)),u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_625,c_25,c_1]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_630,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/0.98      | ~ m1_subset_1(k1_yellow_0(X0,k5_waybel_0(X0,X1)),u1_struct_0(X0))
% 3.97/0.98      | ~ v1_lattice3(X0)
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(X0,X1))
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | ~ v4_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_629]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_14,plain,
% 3.97/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.97/0.98      | ~ l1_orders_2(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_659,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/0.98      | ~ v1_lattice3(X0)
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(X0,X1))
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | ~ v4_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0) ),
% 3.97/0.98      inference(forward_subsumption_resolution,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_630,c_14]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_50,negated_conjecture,
% 3.97/0.98      ( v4_orders_2(sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1309,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/0.98      | ~ v1_lattice3(X0)
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(X0,X1))
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0)
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_659,c_50]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1310,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.97/0.98      | ~ v1_lattice3(sK6)
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(sK6,X0))
% 3.97/0.98      | ~ v3_orders_2(sK6)
% 3.97/0.98      | ~ v5_orders_2(sK6)
% 3.97/0.98      | ~ l1_orders_2(sK6)
% 3.97/0.98      | ~ v2_lattice3(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_1309]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_48,negated_conjecture,
% 3.97/0.98      ( v1_lattice3(sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1314,plain,
% 3.97/0.98      ( ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
% 3.97/0.98      | ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(sK6,X0)) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_1310,c_51,c_49,c_48,c_47,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1315,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.97/0.98      | v1_xboole_0(k5_waybel_0(sK6,X0)) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_1314]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1512,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ m1_subset_1(k5_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.97/0.98      inference(backward_subsumption_resolution,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_1497,c_1315]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_2872,plain,
% 3.97/0.98      ( ~ v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(backward_subsumption_resolution,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_2786,c_1512]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_5100,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6) != iProver_top
% 3.97/0.98      | v4_waybel_7(k1_yellow_0(sK6,k5_waybel_0(sK6,X0)),sK6) = iProver_top
% 3.97/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2872]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_15869,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(sK6,sK7),sK6) != iProver_top
% 3.97/0.98      | v4_waybel_7(sK7,sK6) = iProver_top
% 3.97/0.98      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(superposition,[status(thm)],[c_15867,c_5100]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_42,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | ~ v5_waybel_6(X1,X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ v1_lattice3(X0)
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | ~ v4_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0) ),
% 3.97/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1336,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.97/0.98      | ~ v5_waybel_6(X1,X0)
% 3.97/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.98      | ~ v1_lattice3(X0)
% 3.97/0.98      | ~ v3_orders_2(X0)
% 3.97/0.98      | ~ v5_orders_2(X0)
% 3.97/0.98      | ~ l1_orders_2(X0)
% 3.97/0.98      | ~ v2_lattice3(X0)
% 3.97/0.98      | sK6 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_42,c_50]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1337,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | ~ v5_waybel_6(X0,sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ v1_lattice3(sK6)
% 3.97/0.98      | ~ v3_orders_2(sK6)
% 3.97/0.98      | ~ v5_orders_2(sK6)
% 3.97/0.98      | ~ l1_orders_2(sK6)
% 3.97/0.98      | ~ v2_lattice3(sK6) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_1336]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1341,plain,
% 3.97/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | ~ v5_waybel_6(X0,sK6)
% 3.97/0.98      | v1_waybel_7(k5_waybel_0(sK6,X0),sK6) ),
% 3.97/0.98      inference(global_propositional_subsumption,
% 3.97/0.98                [status(thm)],
% 3.97/0.98                [c_1337,c_51,c_49,c_48,c_47,c_46]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_1342,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | ~ v5_waybel_6(X0,sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(renaming,[status(thm)],[c_1341]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_3284,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(sK6,X0),sK6)
% 3.97/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.97/0.98      | sK6 != sK6
% 3.97/0.98      | sK7 != X0 ),
% 3.97/0.98      inference(resolution_lifted,[status(thm)],[c_44,c_1342]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_3285,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(sK6,sK7),sK6)
% 3.97/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.97/0.98      inference(unflattening,[status(thm)],[c_3284]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_3286,plain,
% 3.97/0.98      ( v1_waybel_7(k5_waybel_0(sK6,sK7),sK6) = iProver_top
% 3.97/0.98      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_3285]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_43,negated_conjecture,
% 3.97/0.98      ( ~ v4_waybel_7(sK7,sK6) ),
% 3.97/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(c_60,plain,
% 3.97/0.98      ( v4_waybel_7(sK7,sK6) != iProver_top ),
% 3.97/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.97/0.98  
% 3.97/0.98  cnf(contradiction,plain,
% 3.97/0.98      ( $false ),
% 3.97/0.98      inference(minisat,[status(thm)],[c_15869,c_3286,c_60,c_58]) ).
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/0.98  
% 3.97/0.98  ------                               Statistics
% 3.97/0.98  
% 3.97/0.98  ------ Selected
% 3.97/0.98  
% 3.97/0.98  total_time:                             0.489
% 3.97/0.98  
%------------------------------------------------------------------------------
