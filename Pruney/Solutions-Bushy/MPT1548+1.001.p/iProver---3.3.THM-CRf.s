%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1548+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:51 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  161 (1129 expanded)
%              Number of clauses        :  108 ( 371 expanded)
%              Number of leaves         :   15 ( 304 expanded)
%              Depth                    :   32
%              Number of atoms          :  778 (5047 expanded)
%              Number of equality atoms :  448 (2258 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   13 (   4 average)
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
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( r1_yellow_0(X0,X2)
                 => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
          & r1_yellow_0(X0,X2) )
     => ( k1_yellow_0(X0,sK3) != k1_yellow_0(X1,sK3)
        & r1_yellow_0(X0,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( k1_yellow_0(sK2,X2) != k1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X2) )
        & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                & r1_yellow_0(X0,X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(sK1,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(sK1,X2) )
          & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3)
    & r1_yellow_0(sK1,sK3)
    & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & l1_orders_2(sK2)
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f30,f29,f28])).

fof(f50,plain,(
    r1_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f45])).

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
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f51,plain,(
    k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( r1_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_621,plain,
    ( r1_yellow_0(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_629,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) = iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_630,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(X0,X1,sK0(X0,X1,X2)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

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

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_622,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r2_lattice3(X1,X2,X3) != iProver_top
    | r2_lattice3(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1525,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(sK2,X1,X2) = iProver_top
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
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(sK2,X1,X2) = iProver_top
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
    | r2_lattice3(sK2,X1,X2) = iProver_top
    | r2_lattice3(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_21])).

cnf(c_2569,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2568])).

cnf(c_2582,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2569])).

cnf(c_3202,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | r2_lattice3(sK2,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_20])).

cnf(c_3203,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3202])).

cnf(c_3211,plain,
    ( k1_yellow_0(sK1,X0) = X1
    | r2_lattice3(sK2,X2,sK0(sK1,X0,X1)) = iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | r2_lattice3(sK1,X2,sK0(sK1,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_3203])).

cnf(c_3417,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_lattice3(sK1,X2,sK0(sK1,X0,X1)) != iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,sK0(sK1,X0,X1)) = iProver_top
    | k1_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3211,c_20])).

cnf(c_3418,plain,
    ( k1_yellow_0(sK1,X0) = X1
    | r2_lattice3(sK2,X2,sK0(sK1,X0,X1)) = iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | r2_lattice3(sK1,X2,sK0(sK1,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3417])).

cnf(c_3429,plain,
    ( k1_yellow_0(sK1,X0) = X1
    | r2_lattice3(sK2,X0,sK0(sK1,X0,X1)) = iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_3418])).

cnf(c_3461,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | r2_lattice3(sK2,X0,sK0(sK1,X0,X1)) = iProver_top
    | k1_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3429,c_20])).

cnf(c_3462,plain,
    ( k1_yellow_0(sK1,X0) = X1
    | r2_lattice3(sK2,X0,sK0(sK1,X0,X1)) = iProver_top
    | r2_lattice3(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3461])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_5])).

cnf(c_112,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_617,plain,
    ( r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112])).

cnf(c_628,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1320,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK1)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_628])).

cnf(c_1945,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_21])).

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

cnf(c_2726,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | r1_orders_2(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2400,c_21])).

cnf(c_2727,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2726])).

cnf(c_2742,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK1,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2727])).

cnf(c_3602,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,X0,X1) = iProver_top
    | r1_orders_2(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_20])).

cnf(c_3603,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK1,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3602])).

cnf(c_3614,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1) != iProver_top
    | r1_orders_2(sK1,k1_yellow_0(sK2,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_3603])).

cnf(c_3770,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK1,k1_yellow_0(sK2,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_3614])).

cnf(c_3771,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK1,k1_yellow_0(sK2,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3770,c_1288])).

cnf(c_3776,plain,
    ( r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,k1_yellow_0(sK2,X0),X1) = iProver_top
    | r2_lattice3(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3771,c_21])).

cnf(c_3777,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK1,k1_yellow_0(sK2,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3776])).

cnf(c_0,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_631,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X2,sK0(X0,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3786,plain,
    ( k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X1)
    | r2_lattice3(sK2,X1,sK0(sK1,X0,k1_yellow_0(sK2,X1))) != iProver_top
    | r2_lattice3(sK1,X0,k1_yellow_0(sK2,X1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3777,c_631])).

cnf(c_3980,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK1)) != iProver_top
    | r2_lattice3(sK1,X0,k1_yellow_0(sK2,X1)) != iProver_top
    | r2_lattice3(sK2,X1,sK0(sK1,X0,k1_yellow_0(sK2,X1))) != iProver_top
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3786,c_20])).

cnf(c_3981,plain,
    ( k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X1)
    | r2_lattice3(sK2,X1,sK0(sK1,X0,k1_yellow_0(sK2,X1))) != iProver_top
    | r2_lattice3(sK1,X0,k1_yellow_0(sK2,X1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3980])).

cnf(c_3993,plain,
    ( k1_yellow_0(sK2,X0) = k1_yellow_0(sK1,X1)
    | r2_lattice3(sK2,X0,sK0(sK1,X1,k1_yellow_0(sK2,X0))) != iProver_top
    | r2_lattice3(sK1,X1,k1_yellow_0(sK2,X0)) != iProver_top
    | m1_subset_1(sK0(sK1,X1,k1_yellow_0(sK2,X0)),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | r1_yellow_0(sK1,X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3981,c_1945])).

cnf(c_3997,plain,
    ( k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X0)
    | r2_lattice3(sK1,X0,k1_yellow_0(sK2,X0)) != iProver_top
    | m1_subset_1(sK0(sK1,X0,k1_yellow_0(sK2,X0)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3462,c_3993])).

cnf(c_10,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X2,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_624,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_yellow_0(X1,X2) != iProver_top
    | r1_yellow_0(X0,X2) = iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1697,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r1_yellow_0(X0,X1) != iProver_top
    | r1_yellow_0(sK2,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_624])).

cnf(c_1723,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_yellow_0(X0,X1) != iProver_top
    | r1_yellow_0(sK2,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1697,c_1288])).

cnf(c_2182,plain,
    ( l1_orders_2(X0) != iProver_top
    | r1_yellow_0(sK2,X1) = iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_21])).

cnf(c_2183,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r1_yellow_0(X0,X1) != iProver_top
    | r1_yellow_0(sK2,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2182])).

cnf(c_2194,plain,
    ( r1_yellow_0(sK2,X0) = iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2183])).

cnf(c_2935,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | r1_yellow_0(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_20])).

cnf(c_2936,plain,
    ( r1_yellow_0(sK2,X0) = iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2935])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_104,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_5])).

cnf(c_618,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) = iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_1527,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK1))
    | r2_lattice3(X0,X1,X2) = iProver_top
    | r2_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_622])).

cnf(c_1536,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r2_lattice3(X0,X1,X2) = iProver_top
    | r2_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1527,c_1288])).

cnf(c_2205,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_lattice3(sK2,X1,X2) != iProver_top
    | r2_lattice3(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1536,c_21])).

cnf(c_2206,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | r2_lattice3(X0,X1,X2) = iProver_top
    | r2_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2205])).

cnf(c_2219,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK1,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2206])).

cnf(c_3026,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_lattice3(sK1,X0,X1) = iProver_top
    | r2_lattice3(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_20])).

cnf(c_3027,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK1,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3026])).

cnf(c_3036,plain,
    ( r2_lattice3(sK1,X0,k1_yellow_0(sK2,X0)) = iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_3027])).

cnf(c_4135,plain,
    ( r1_yellow_0(sK2,X0) != iProver_top
    | r2_lattice3(sK1,X0,k1_yellow_0(sK2,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3036,c_21,c_1320])).

cnf(c_4136,plain,
    ( r2_lattice3(sK1,X0,k1_yellow_0(sK2,X0)) = iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4135])).

cnf(c_4725,plain,
    ( k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X0)
    | m1_subset_1(sK0(sK1,X0,k1_yellow_0(sK2,X0)),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3997,c_21,c_1320,c_2936,c_4136])).

cnf(c_4734,plain,
    ( k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X0)
    | r2_lattice3(sK1,X0,k1_yellow_0(sK2,X0)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_4725])).

cnf(c_4972,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4734,c_20,c_21,c_1320,c_2194,c_3036])).

cnf(c_4973,plain,
    ( k1_yellow_0(sK1,X0) = k1_yellow_0(sK2,X0)
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4972])).

cnf(c_4980,plain,
    ( k1_yellow_0(sK2,sK3) = k1_yellow_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_621,c_4973])).

cnf(c_313,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_793,plain,
    ( k1_yellow_0(sK2,sK3) != X0
    | k1_yellow_0(sK1,sK3) != X0
    | k1_yellow_0(sK1,sK3) = k1_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_892,plain,
    ( k1_yellow_0(sK2,sK3) != k1_yellow_0(X0,X1)
    | k1_yellow_0(sK1,sK3) != k1_yellow_0(X0,X1)
    | k1_yellow_0(sK1,sK3) = k1_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1631,plain,
    ( k1_yellow_0(sK2,sK3) != k1_yellow_0(sK1,sK3)
    | k1_yellow_0(sK1,sK3) = k1_yellow_0(sK2,sK3)
    | k1_yellow_0(sK1,sK3) != k1_yellow_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_314,plain,
    ( X0 != X1
    | X2 != X3
    | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X3) ),
    theory(equality)).

cnf(c_998,plain,
    ( X0 != sK3
    | X1 != sK1
    | k1_yellow_0(X1,X0) = k1_yellow_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1388,plain,
    ( X0 != sK1
    | k1_yellow_0(X0,sK3) = k1_yellow_0(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1389,plain,
    ( k1_yellow_0(sK1,sK3) = k1_yellow_0(sK1,sK3)
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
    ( k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4980,c_1631,c_1389,c_879,c_337,c_15])).


%------------------------------------------------------------------------------
