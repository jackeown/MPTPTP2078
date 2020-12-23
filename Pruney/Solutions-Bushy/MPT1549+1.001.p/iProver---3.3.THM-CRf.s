%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:52 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  188 (1444 expanded)
%              Number of clauses        :  135 ( 468 expanded)
%              Number of leaves         :   15 ( 387 expanded)
%              Depth                    :   31
%              Number of atoms          :  975 (6762 expanded)
%              Number of equality atoms :  645 (3013 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( r2_yellow_0(X0,X2)
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
          & r2_yellow_0(X0,X2) )
     => ( k2_yellow_0(X0,sK3) != k2_yellow_0(X1,sK3)
        & r2_yellow_0(X0,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( k2_yellow_0(sK2,X2) != k2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X2) )
        & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                & r2_yellow_0(X0,X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(sK1,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(sK1,X2) )
          & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_yellow_0(sK1,sK3) != k2_yellow_0(sK2,sK3)
    & r2_yellow_0(sK1,sK3)
    & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & l1_orders_2(sK2)
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f30,f29,f28])).

fof(f50,plain,(
    r2_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | r1_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
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
    inference(equality_resolution,[],[f43])).

fof(f57,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( r2_yellow_0(X0,X2)
                 => r2_yellow_0(X1,X2) )
                & ( r1_yellow_0(X0,X2)
                 => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f51,plain,(
    k2_yellow_0(sK1,sK3) != k2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( r2_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_621,plain,
    ( r2_yellow_0(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_630,plain,
    ( k2_yellow_0(X0,X1) = X2
    | r1_lattice3(X0,X1,X2) != iProver_top
    | r1_lattice3(X0,X1,sK0(X0,X1,X2)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_629,plain,
    ( k2_yellow_0(X0,X1) = X2
    | r1_lattice3(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) = iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_626,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1142,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_626])).

cnf(c_1217,plain,
    ( u1_orders_2(sK2) = u1_orders_2(sK1)
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1142])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_33,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_35,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1411,plain,
    ( u1_orders_2(sK2) = u1_orders_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1217,c_20,c_35])).

cnf(c_13,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_622,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_lattice3(X1,X2,X3) != iProver_top
    | r1_lattice3(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1525,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r1_lattice3(X0,X1,X2) != iProver_top
    | r1_lattice3(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_622])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_625,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1024,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_625])).

cnf(c_1168,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1024])).

cnf(c_1288,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1168,c_20,c_35])).

cnf(c_1559,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_lattice3(X0,X1,X2) != iProver_top
    | r1_lattice3(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1525,c_1288])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2568,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_lattice3(sK2,X1,X2) = iProver_top
    | r1_lattice3(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_21])).

cnf(c_2569,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_lattice3(X0,X1,X2) != iProver_top
    | r1_lattice3(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2568])).

cnf(c_2582,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2569])).

cnf(c_3201,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_lattice3(sK2,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_20])).

cnf(c_3202,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3201])).

cnf(c_3210,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) = iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_lattice3(sK1,X2,sK0(sK1,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_3202])).

cnf(c_3416,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_lattice3(sK1,X2,sK0(sK1,X0,X1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) = iProver_top
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_20])).

cnf(c_3417,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) = iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_lattice3(sK1,X2,sK0(sK1,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3416])).

cnf(c_3428,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X0,sK0(sK1,X0,X1)) = iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_3417])).

cnf(c_3460,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_lattice3(sK2,X0,sK0(sK1,X0,X1)) = iProver_top
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3428,c_20])).

cnf(c_3461,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X0,sK0(sK1,X0,X1)) = iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3460])).

cnf(c_3,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_5])).

cnf(c_112,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_617,plain,
    ( r1_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_623,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_orders_2(X1,X2,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2389,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_623])).

cnf(c_2400,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2389,c_1288])).

cnf(c_2724,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | r1_orders_2(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2400,c_21])).

cnf(c_2725,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2724])).

cnf(c_2740,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK1,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2725])).

cnf(c_3601,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,X0,X1) = iProver_top
    | r1_orders_2(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2740,c_20])).

cnf(c_3602,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK1,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3601])).

cnf(c_3611,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_orders_2(sK2,sK0(sK1,X0,X1),X2) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_3602])).

cnf(c_4268,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),X2) = iProver_top
    | r1_orders_2(sK2,sK0(sK1,X0,X1),X2) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3611,c_20])).

cnf(c_4269,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_orders_2(sK2,sK0(sK1,X0,X1),X2) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4268])).

cnf(c_4281,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),k2_yellow_0(sK2,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X2),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X2) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_4269])).

cnf(c_4282,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),k2_yellow_0(sK2,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X2),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X2) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4281,c_1288])).

cnf(c_4431,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | r2_yellow_0(sK2,X2) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),k2_yellow_0(sK2,X2)) = iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) != iProver_top
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4282,c_21])).

cnf(c_4432,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),k2_yellow_0(sK2,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X2),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X2) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4431])).

cnf(c_628,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1320,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK1)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_628])).

cnf(c_1945,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_21])).

cnf(c_4446,plain,
    ( k2_yellow_0(sK1,X0) = X1
    | r1_lattice3(sK2,X2,sK0(sK1,X0,X1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0,X1),k2_yellow_0(sK2,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X2) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4432,c_1945])).

cnf(c_0,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_631,plain,
    ( k2_yellow_0(X0,X1) = X2
    | r1_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,sK0(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4450,plain,
    ( k2_yellow_0(sK2,X0) = k2_yellow_0(sK1,X1)
    | r1_lattice3(sK2,X0,sK0(sK1,X1,k2_yellow_0(sK2,X0))) != iProver_top
    | r1_lattice3(sK1,X1,k2_yellow_0(sK2,X0)) != iProver_top
    | m1_subset_1(sK0(sK1,X1,k2_yellow_0(sK2,X0)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4446,c_631])).

cnf(c_5059,plain,
    ( r2_yellow_0(sK1,X1) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | k2_yellow_0(sK2,X0) = k2_yellow_0(sK1,X1)
    | r1_lattice3(sK2,X0,sK0(sK1,X1,k2_yellow_0(sK2,X0))) != iProver_top
    | r1_lattice3(sK1,X1,k2_yellow_0(sK2,X0)) != iProver_top
    | m1_subset_1(sK0(sK1,X1,k2_yellow_0(sK2,X0)),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4450,c_20,c_21,c_1320])).

cnf(c_5060,plain,
    ( k2_yellow_0(sK2,X0) = k2_yellow_0(sK1,X1)
    | r1_lattice3(sK2,X0,sK0(sK1,X1,k2_yellow_0(sK2,X0))) != iProver_top
    | r1_lattice3(sK1,X1,k2_yellow_0(sK2,X0)) != iProver_top
    | m1_subset_1(sK0(sK1,X1,k2_yellow_0(sK2,X0)),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5059])).

cnf(c_5071,plain,
    ( k2_yellow_0(sK1,X0) = k2_yellow_0(sK2,X0)
    | r1_lattice3(sK1,X0,k2_yellow_0(sK2,X0)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,k2_yellow_0(sK2,X0)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_5060])).

cnf(c_1527,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r1_lattice3(X0,X1,X2) = iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_622])).

cnf(c_1536,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_lattice3(X0,X1,X2) = iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1527,c_1288])).

cnf(c_2205,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | r1_lattice3(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1536,c_21])).

cnf(c_2206,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_lattice3(X0,X1,X2) = iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2205])).

cnf(c_2219,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2206])).

cnf(c_3022,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_lattice3(sK1,X0,X1) = iProver_top
    | r1_lattice3(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_20])).

cnf(c_3023,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3022])).

cnf(c_3031,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X0,sK0(sK2,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_3023])).

cnf(c_3048,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X0,sK0(sK2,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3031,c_1288])).

cnf(c_1748,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK1)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_629])).

cnf(c_1749,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK1)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1748,c_1288])).

cnf(c_3189,plain,
    ( r2_yellow_0(sK2,X0) != iProver_top
    | k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X0,sK0(sK2,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3048,c_21,c_1749])).

cnf(c_3190,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X0,sK0(sK2,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3189])).

cnf(c_2556,plain,
    ( r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1749,c_21])).

cnf(c_2557,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK1)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2556])).

cnf(c_2387,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_623])).

cnf(c_2429,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2387,c_1288])).

cnf(c_2755,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | r1_orders_2(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2429,c_21])).

cnf(c_2756,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2755])).

cnf(c_2771,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2756])).

cnf(c_3812,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,X0,X1) != iProver_top
    | r1_orders_2(sK2,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2771,c_20])).

cnf(c_3813,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3812])).

cnf(c_3825,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),X2) = iProver_top
    | r1_orders_2(sK1,sK0(sK2,X0,X1),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_3813])).

cnf(c_4819,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X2,sK0(sK2,X0,X1)) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),k2_yellow_0(sK1,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X2),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X2) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_3825])).

cnf(c_5693,plain,
    ( r2_yellow_0(sK1,X2) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X2),u1_struct_0(sK1)) != iProver_top
    | k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X2,sK0(sK2,X0,X1)) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),k2_yellow_0(sK1,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4819,c_20,c_21,c_1749])).

cnf(c_5694,plain,
    ( k2_yellow_0(sK2,X0) = X1
    | r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK1,X2,sK0(sK2,X0,X1)) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),k2_yellow_0(sK1,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X2),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5693])).

cnf(c_5707,plain,
    ( k2_yellow_0(sK1,X0) = k2_yellow_0(sK2,X1)
    | r1_lattice3(sK2,X1,k2_yellow_0(sK1,X0)) != iProver_top
    | r1_lattice3(sK1,X0,sK0(sK2,X1,k2_yellow_0(sK1,X0))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X1) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5694,c_631])).

cnf(c_5733,plain,
    ( k2_yellow_0(sK2,X0) = k2_yellow_0(sK1,X1)
    | r1_lattice3(sK2,X0,k2_yellow_0(sK1,X1)) != iProver_top
    | r1_lattice3(sK1,X1,sK0(sK2,X0,k2_yellow_0(sK1,X1))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X1),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5707,c_1288])).

cnf(c_5897,plain,
    ( r2_yellow_0(sK1,X1) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X1),u1_struct_0(sK1)) != iProver_top
    | r1_lattice3(sK1,X1,sK0(sK2,X0,k2_yellow_0(sK1,X1))) != iProver_top
    | r1_lattice3(sK2,X0,k2_yellow_0(sK1,X1)) != iProver_top
    | k2_yellow_0(sK2,X0) = k2_yellow_0(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5733,c_21])).

cnf(c_5898,plain,
    ( k2_yellow_0(sK2,X0) = k2_yellow_0(sK1,X1)
    | r1_lattice3(sK2,X0,k2_yellow_0(sK1,X1)) != iProver_top
    | r1_lattice3(sK1,X1,sK0(sK2,X0,k2_yellow_0(sK1,X1))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X1),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5897])).

cnf(c_5909,plain,
    ( k2_yellow_0(sK1,X0) = k2_yellow_0(sK2,X0)
    | r1_lattice3(sK2,X0,k2_yellow_0(sK1,X0)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_5898])).

cnf(c_9,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r2_yellow_0(X2,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_624,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r2_yellow_0(X1,X2) != iProver_top
    | r2_yellow_0(X0,X2) = iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1697,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r2_yellow_0(X0,X1) != iProver_top
    | r2_yellow_0(sK2,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_624])).

cnf(c_1723,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r2_yellow_0(X0,X1) != iProver_top
    | r2_yellow_0(sK2,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1697,c_1288])).

cnf(c_2182,plain,
    ( l1_orders_2(X0) != iProver_top
    | r2_yellow_0(sK2,X1) = iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_21])).

cnf(c_2183,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r2_yellow_0(X0,X1) != iProver_top
    | r2_yellow_0(sK2,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2182])).

cnf(c_2194,plain,
    ( r2_yellow_0(sK2,X0) = iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2183])).

cnf(c_2933,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | r2_yellow_0(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_20])).

cnf(c_2934,plain,
    ( r2_yellow_0(sK2,X0) = iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2933])).

cnf(c_4,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_104,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_5])).

cnf(c_618,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) = iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_3211,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK1,X1)) = iProver_top
    | r1_lattice3(sK1,X0,k2_yellow_0(sK1,X1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_3202])).

cnf(c_3403,plain,
    ( r1_lattice3(sK1,X0,k2_yellow_0(sK1,X1)) != iProver_top
    | r1_lattice3(sK2,X0,k2_yellow_0(sK1,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3211,c_20])).

cnf(c_3404,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK1,X1)) = iProver_top
    | r1_lattice3(sK1,X0,k2_yellow_0(sK1,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3403])).

cnf(c_3411,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK1,X0)) = iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_3404])).

cnf(c_5914,plain,
    ( m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1)) != iProver_top
    | k2_yellow_0(sK1,X0) = k2_yellow_0(sK2,X0)
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5909,c_20,c_2934,c_3411])).

cnf(c_5915,plain,
    ( k2_yellow_0(sK1,X0) = k2_yellow_0(sK2,X0)
    | m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1)) != iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5914])).

cnf(c_5923,plain,
    ( k2_yellow_0(sK1,X0) = k2_yellow_0(sK2,X0)
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_5915])).

cnf(c_6047,plain,
    ( k2_yellow_0(sK1,X0) = k2_yellow_0(sK2,X0)
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5071,c_20,c_5923])).

cnf(c_6055,plain,
    ( k2_yellow_0(sK2,sK3) = k2_yellow_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_621,c_6047])).

cnf(c_313,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_793,plain,
    ( k2_yellow_0(sK2,sK3) != X0
    | k2_yellow_0(sK1,sK3) != X0
    | k2_yellow_0(sK1,sK3) = k2_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_892,plain,
    ( k2_yellow_0(sK2,sK3) != k2_yellow_0(X0,X1)
    | k2_yellow_0(sK1,sK3) != k2_yellow_0(X0,X1)
    | k2_yellow_0(sK1,sK3) = k2_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1631,plain,
    ( k2_yellow_0(sK2,sK3) != k2_yellow_0(sK1,sK3)
    | k2_yellow_0(sK1,sK3) = k2_yellow_0(sK2,sK3)
    | k2_yellow_0(sK1,sK3) != k2_yellow_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_314,plain,
    ( X0 != X1
    | X2 != X3
    | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X3) ),
    theory(equality)).

cnf(c_998,plain,
    ( X0 != sK3
    | X1 != sK1
    | k2_yellow_0(X1,X0) = k2_yellow_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1388,plain,
    ( X0 != sK1
    | k2_yellow_0(X0,sK3) = k2_yellow_0(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1389,plain,
    ( k2_yellow_0(sK1,sK3) = k2_yellow_0(sK1,sK3)
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_312,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_879,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_337,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_15,negated_conjecture,
    ( k2_yellow_0(sK1,sK3) != k2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6055,c_1631,c_1389,c_879,c_337,c_15])).


%------------------------------------------------------------------------------
