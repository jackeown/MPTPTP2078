%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1535+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:48 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  124 (1325 expanded)
%              Number of clauses        :   79 ( 407 expanded)
%              Number of leaves         :   10 ( 321 expanded)
%              Depth                    :   21
%              Number of atoms          :  505 (7326 expanded)
%              Number of equality atoms :  243 (1801 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ( ( v2_yellow_0(X0)
               => v2_yellow_0(X1) )
              & ( v1_yellow_0(X0)
               => v1_yellow_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ( ( v2_yellow_0(X0)
                 => v2_yellow_0(X1) )
                & ( v1_yellow_0(X0)
                 => v1_yellow_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ( ( ~ v2_yellow_0(sK3)
            & v2_yellow_0(X0) )
          | ( ~ v1_yellow_0(sK3)
            & v1_yellow_0(X0) ) )
        & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v2_yellow_0(X1)
                & v2_yellow_0(X0) )
              | ( ~ v1_yellow_0(X1)
                & v1_yellow_0(X0) ) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(sK2) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(sK2) ) )
          & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ( ~ v2_yellow_0(sK3)
        & v2_yellow_0(sK2) )
      | ( ~ v1_yellow_0(sK3)
        & v1_yellow_0(sK2) ) )
    & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & l1_orders_2(sK3)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f25,f24])).

fof(f40,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f28,plain,(
    ! [X0] :
      ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,
    ( v2_yellow_0(sK2)
    | v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,
    ( ~ v2_yellow_0(sK3)
    | v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r2_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r2_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r2_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_yellow_0(X0)
      | ~ r2_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0] :
      ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_yellow_0(X0)
      | ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,
    ( v2_yellow_0(sK2)
    | ~ v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,
    ( ~ v2_yellow_0(sK3)
    | ~ v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_926,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1992,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_926])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_31,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1993,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_926])).

cnf(c_2010,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1993])).

cnf(c_2131,plain,
    ( u1_struct_0(sK2) = X0
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1992,c_17,c_31,c_2010])).

cnf(c_2132,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2131])).

cnf(c_2137,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(equality_resolution,[status(thm)],[c_2132])).

cnf(c_1,plain,
    ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_yellow_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_933,plain,
    ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2479,plain,
    ( r1_lattice3(sK2,u1_struct_0(sK3),sK0(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top
    | v1_yellow_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_933])).

cnf(c_18,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( v2_yellow_0(sK2)
    | v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,plain,
    ( v2_yellow_0(sK2) = iProver_top
    | v1_yellow_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( ~ v2_yellow_0(sK3)
    | v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,plain,
    ( v2_yellow_0(sK3) != iProver_top
    | v1_yellow_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1099,plain,
    ( ~ r2_lattice3(sK3,u1_struct_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_yellow_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1656,plain,
    ( ~ r2_lattice3(sK3,u1_struct_0(sK3),sK1(X0))
    | ~ m1_subset_1(sK1(X0),u1_struct_0(sK3))
    | v2_yellow_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_1661,plain,
    ( r2_lattice3(sK3,u1_struct_0(sK3),sK1(X0)) != iProver_top
    | m1_subset_1(sK1(X0),u1_struct_0(sK3)) != iProver_top
    | v2_yellow_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_1663,plain,
    ( r2_lattice3(sK3,u1_struct_0(sK3),sK1(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_yellow_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_4,plain,
    ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_930,plain,
    ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0)) = iProver_top
    | v2_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_924,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r2_lattice3(X1,X2,X3) != iProver_top
    | r2_lattice3(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1264,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r2_lattice3(X0,X1,X2) = iProver_top
    | r2_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_924])).

cnf(c_1531,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_lattice3(sK2,X1,X2) != iProver_top
    | r2_lattice3(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1264,c_18])).

cnf(c_1532,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r2_lattice3(X0,X1,X2) = iProver_top
    | r2_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1531])).

cnf(c_1542,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1532])).

cnf(c_1689,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r2_lattice3(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_19])).

cnf(c_1690,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1689])).

cnf(c_1699,plain,
    ( r2_lattice3(sK3,u1_struct_0(sK2),sK1(sK2)) = iProver_top
    | m1_subset_1(sK1(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_yellow_0(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_1690])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_33,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0)) = iProver_top
    | v2_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_35,plain,
    ( m1_subset_1(sK1(sK2),u1_struct_0(sK2)) = iProver_top
    | v2_yellow_0(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1795,plain,
    ( v2_yellow_0(sK2) != iProver_top
    | m1_subset_1(sK1(sK2),u1_struct_0(sK3)) != iProver_top
    | r2_lattice3(sK3,u1_struct_0(sK2),sK1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1699,c_18,c_35])).

cnf(c_1796,plain,
    ( r2_lattice3(sK3,u1_struct_0(sK2),sK1(sK2)) = iProver_top
    | m1_subset_1(sK1(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_yellow_0(sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1795])).

cnf(c_2388,plain,
    ( r2_lattice3(sK3,u1_struct_0(sK3),sK1(sK2)) = iProver_top
    | m1_subset_1(sK1(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_yellow_0(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2137,c_1796])).

cnf(c_929,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0)) = iProver_top
    | v2_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2482,plain,
    ( m1_subset_1(sK1(sK2),u1_struct_0(sK3)) = iProver_top
    | v2_yellow_0(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_929])).

cnf(c_3414,plain,
    ( r1_lattice3(sK2,u1_struct_0(sK3),sK0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2479,c_18,c_19,c_20,c_22,c_1663,c_2388,c_2482])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_yellow_0(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_932,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2481,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK3)) = iProver_top
    | l1_orders_2(sK2) != iProver_top
    | v1_yellow_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_932])).

cnf(c_2899,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2481,c_18,c_19,c_20,c_22,c_1663,c_2388,c_2482])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_925,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_lattice3(X1,X2,X3) != iProver_top
    | r1_lattice3(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1879,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_lattice3(X0,X1,X2) = iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_925])).

cnf(c_2273,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | r1_lattice3(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1879,c_18])).

cnf(c_2274,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_lattice3(X0,X1,X2) = iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2273])).

cnf(c_2284,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2274])).

cnf(c_3109,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | r1_lattice3(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2284,c_19])).

cnf(c_3110,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3109])).

cnf(c_3115,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3110,c_2137])).

cnf(c_3124,plain,
    ( r1_lattice3(sK2,X0,sK0(sK2)) != iProver_top
    | r1_lattice3(sK3,X0,sK0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2899,c_3115])).

cnf(c_4114,plain,
    ( r1_lattice3(sK3,u1_struct_0(sK3),sK0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3414,c_3124])).

cnf(c_0,plain,
    ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v1_yellow_0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_934,plain,
    ( r1_lattice3(X0,u1_struct_0(X0),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4222,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_yellow_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4114,c_934])).

cnf(c_1878,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_lattice3(X0,X1,X2) != iProver_top
    | r1_lattice3(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_925])).

cnf(c_2247,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_lattice3(sK2,X1,X2) = iProver_top
    | r1_lattice3(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1878,c_18])).

cnf(c_2248,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_lattice3(X0,X1,X2) != iProver_top
    | r1_lattice3(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2247])).

cnf(c_2258,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2248])).

cnf(c_3053,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK3,X0,X1) != iProver_top
    | r1_lattice3(sK2,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2258,c_19])).

cnf(c_3054,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3053])).

cnf(c_3059,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3054,c_2137])).

cnf(c_3066,plain,
    ( r1_lattice3(sK2,X0,sK0(sK3)) = iProver_top
    | r1_lattice3(sK3,X0,sK0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_yellow_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_3059])).

cnf(c_13,negated_conjecture,
    ( v2_yellow_0(sK2)
    | ~ v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,plain,
    ( v2_yellow_0(sK2) = iProver_top
    | v1_yellow_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( ~ v2_yellow_0(sK3)
    | ~ v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,plain,
    ( v2_yellow_0(sK3) != iProver_top
    | v1_yellow_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3420,plain,
    ( v1_yellow_0(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3066,c_18,c_19,c_21,c_23,c_1663,c_2388,c_2482])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4222,c_3420,c_2899,c_19])).


%------------------------------------------------------------------------------
