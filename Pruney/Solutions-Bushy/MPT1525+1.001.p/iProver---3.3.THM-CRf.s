%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1525+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:46 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  131 (1135 expanded)
%              Number of clauses        :   86 ( 332 expanded)
%              Number of leaves         :   11 ( 296 expanded)
%              Depth                    :   30
%              Number of atoms          :  622 (5556 expanded)
%              Number of equality atoms :  311 (1521 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f30,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | m1_subset_1(sK1(X0,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | r2_lattice3(X0,sK0(X0),sK1(X0,X2))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ~ v3_lattice3(sK4)
        & v3_lattice3(X0)
        & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_lattice3(X1)
            & v3_lattice3(X0)
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(sK3)
          & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v3_lattice3(sK4)
    & v3_lattice3(sK3)
    & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    & l1_orders_2(sK4)
    & l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f25,f24])).

fof(f42,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f40,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ~ v3_lattice3(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X6,X4,X0] :
      ( r1_orders_2(X0,sK2(X0,X4),X6)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK2(X0,X4),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    v3_lattice3(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f32,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | ~ r1_orders_2(X0,X2,sK1(X0,X2))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK2(X0,X4))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1316,plain,
    ( r2_lattice3(X0,sK0(X0),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_lattice3(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1317,plain,
    ( r2_lattice3(X0,sK0(X0),X1) != iProver_top
    | r2_lattice3(X0,sK0(X0),sK1(X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_lattice3(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1308,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r2_lattice3(X1,X2,X3) != iProver_top
    | r2_lattice3(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1698,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(sK3,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1308])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1946,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_lattice3(sK3,X1,X2) = iProver_top
    | r2_lattice3(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1698,c_18])).

cnf(c_1947,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(sK3,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1946])).

cnf(c_1957,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r2_lattice3(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1947])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2704,plain,
    ( m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_lattice3(sK4,X0,X1) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1957,c_19])).

cnf(c_2705,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r2_lattice3(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2704])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1310,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1735,plain,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK3) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1310])).

cnf(c_6,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_31,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1736,plain,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK3) = X0
    | m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1310])).

cnf(c_1753,plain,
    ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK3) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1736])).

cnf(c_1832,plain,
    ( u1_struct_0(sK3) = X0
    | g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1735,c_17,c_31,c_1753])).

cnf(c_1833,plain,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1832])).

cnf(c_1838,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1833])).

cnf(c_2710,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r2_lattice3(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2705,c_1838])).

cnf(c_2717,plain,
    ( r2_lattice3(sK3,sK0(sK4),sK1(sK4,X0)) = iProver_top
    | r2_lattice3(sK4,sK0(sK4),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top
    | v3_lattice3(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_2710])).

cnf(c_13,negated_conjecture,
    ( ~ v3_lattice3(sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( v3_lattice3(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_374,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_375,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_376,plain,
    ( r2_lattice3(sK4,sK0(sK4),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_3081,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_lattice3(sK4,sK0(sK4),X0) != iProver_top
    | r2_lattice3(sK3,sK0(sK4),sK1(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2717,c_19,c_21,c_376])).

cnf(c_3082,plain,
    ( r2_lattice3(sK3,sK0(sK4),sK1(sK4,X0)) = iProver_top
    | r2_lattice3(sK4,sK0(sK4),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3081])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK2(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1315,plain,
    ( r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,sK2(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1313,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2146,plain,
    ( m1_subset_1(sK2(sK3,X0),u1_struct_0(sK4)) = iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v3_lattice3(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1313])).

cnf(c_14,negated_conjecture,
    ( v3_lattice3(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,plain,
    ( v3_lattice3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2909,plain,
    ( m1_subset_1(sK2(sK3,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2146,c_18,c_20])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1311,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1810,plain,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK3) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1311])).

cnf(c_1811,plain,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK3) = X1
    | m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1311])).

cnf(c_1828,plain,
    ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK3) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1811])).

cnf(c_1928,plain,
    ( u1_orders_2(sK3) = X1
    | g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1810,c_17,c_31,c_1828])).

cnf(c_1929,plain,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK3) = X1 ),
    inference(renaming,[status(thm)],[c_1928])).

cnf(c_1934,plain,
    ( u1_orders_2(sK4) = u1_orders_2(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1929])).

cnf(c_10,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1309,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_orders_2(X1,X2,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2364,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK3,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1934,c_1309])).

cnf(c_2375,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK3,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2364,c_1838])).

cnf(c_3107,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK3,X1,X2) != iProver_top
    | r1_orders_2(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2375,c_18])).

cnf(c_3108,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK3,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3107])).

cnf(c_3121,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK4,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3108])).

cnf(c_3316,plain,
    ( m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_orders_2(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK3,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3121,c_19])).

cnf(c_3317,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK4,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3316])).

cnf(c_3328,plain,
    ( r1_orders_2(sK3,sK2(sK3,X0),X1) != iProver_top
    | r1_orders_2(sK4,sK2(sK3,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_3317])).

cnf(c_3441,plain,
    ( r2_lattice3(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK4,sK2(sK3,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v3_lattice3(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_3328])).

cnf(c_3442,plain,
    ( r2_lattice3(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK4,sK2(sK3,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v3_lattice3(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3441,c_1838])).

cnf(c_3519,plain,
    ( r2_lattice3(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK4,sK2(sK3,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3442,c_18,c_20])).

cnf(c_0,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ r1_orders_2(X0,X1,sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1318,plain,
    ( r2_lattice3(X0,sK0(X0),X1) != iProver_top
    | r1_orders_2(X0,X1,sK1(X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_lattice3(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3528,plain,
    ( r2_lattice3(sK3,X0,sK1(sK4,sK2(sK3,X0))) != iProver_top
    | r2_lattice3(sK4,sK0(sK4),sK2(sK3,X0)) != iProver_top
    | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK2(sK3,X0)),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top
    | v3_lattice3(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3519,c_1318])).

cnf(c_3533,plain,
    ( r2_lattice3(sK4,sK0(sK4),sK2(sK3,X0)) != iProver_top
    | r2_lattice3(sK3,X0,sK1(sK4,sK2(sK3,X0))) != iProver_top
    | m1_subset_1(sK1(sK4,sK2(sK3,X0)),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3528,c_18,c_19,c_20,c_21,c_2146])).

cnf(c_3534,plain,
    ( r2_lattice3(sK3,X0,sK1(sK4,sK2(sK3,X0))) != iProver_top
    | r2_lattice3(sK4,sK0(sK4),sK2(sK3,X0)) != iProver_top
    | m1_subset_1(sK1(sK4,sK2(sK3,X0)),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3533])).

cnf(c_3542,plain,
    ( r2_lattice3(sK4,sK0(sK4),sK2(sK3,sK0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK3,sK0(sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK2(sK3,sK0(sK4))),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_3534])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1314,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1699,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | r2_lattice3(X0,X1,X2) = iProver_top
    | r2_lattice3(sK3,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1308])).

cnf(c_2088,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_lattice3(sK3,X1,X2) != iProver_top
    | r2_lattice3(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1699,c_18])).

cnf(c_2089,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | r2_lattice3(X0,X1,X2) = iProver_top
    | r2_lattice3(sK3,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2088])).

cnf(c_2099,plain,
    ( r2_lattice3(sK3,X0,X1) != iProver_top
    | r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2089])).

cnf(c_2825,plain,
    ( m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_lattice3(sK4,X0,X1) = iProver_top
    | r2_lattice3(sK3,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2099,c_19])).

cnf(c_2826,plain,
    ( r2_lattice3(sK3,X0,X1) != iProver_top
    | r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2825])).

cnf(c_2831,plain,
    ( r2_lattice3(sK3,X0,X1) != iProver_top
    | r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2826,c_1838])).

cnf(c_2839,plain,
    ( r2_lattice3(sK4,X0,sK2(sK3,X0)) = iProver_top
    | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v3_lattice3(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_2831])).

cnf(c_3002,plain,
    ( r2_lattice3(sK4,X0,sK2(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2839,c_18,c_20,c_2146])).

cnf(c_3746,plain,
    ( m1_subset_1(sK1(sK4,sK2(sK3,sK0(sK4))),u1_struct_0(sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3542,c_2909,c_3002])).

cnf(c_3748,plain,
    ( r2_lattice3(sK4,sK0(sK4),sK2(sK3,sK0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK3,sK0(sK4)),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top
    | v3_lattice3(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_3746])).

cnf(c_3872,plain,
    ( r2_lattice3(sK4,sK0(sK4),sK2(sK3,sK0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK3,sK0(sK4)),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3748,c_19,c_21])).

cnf(c_3878,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3872,c_2909,c_3002])).


%------------------------------------------------------------------------------
