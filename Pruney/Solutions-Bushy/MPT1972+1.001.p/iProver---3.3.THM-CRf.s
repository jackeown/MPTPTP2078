%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1972+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:58 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  310 (2463 expanded)
%              Number of clauses        :  217 ( 615 expanded)
%              Number of leaves         :   15 ( 546 expanded)
%              Depth                    :   18
%              Number of atoms          : 2009 (40249 expanded)
%              Number of equality atoms :  680 (1021 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   52 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
     => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          | ~ v1_waybel_7(sK3,k7_lattice3(X0))
          | ~ v12_waybel_0(sK3,k7_lattice3(X0))
          | ~ v1_waybel_0(sK3,k7_lattice3(X0))
          | v1_xboole_0(sK3)
          | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v2_waybel_7(sK3,X0)
          | ~ v13_waybel_0(sK3,X0)
          | ~ v2_waybel_0(sK3,X0)
          | v1_xboole_0(sK3) )
        & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(sK3,k7_lattice3(X0))
            & v12_waybel_0(sK3,k7_lattice3(X0))
            & v1_waybel_0(sK3,k7_lattice3(X0))
            & ~ v1_xboole_0(sK3) )
          | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(sK3,X0)
            & v13_waybel_0(sK3,X0)
            & v2_waybel_0(sK3,X0)
            & ~ v1_xboole_0(sK3) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              | ~ v1_waybel_7(X1,k7_lattice3(X0))
              | ~ v12_waybel_0(X1,k7_lattice3(X0))
              | ~ v1_waybel_0(X1,k7_lattice3(X0))
              | v1_xboole_0(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X1,X0)
              | ~ v13_waybel_0(X1,X0)
              | ~ v2_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
                & v1_waybel_7(X1,k7_lattice3(X0))
                & v12_waybel_0(X1,k7_lattice3(X0))
                & v1_waybel_0(X1,k7_lattice3(X0))
                & ~ v1_xboole_0(X1) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_waybel_7(X1,X0)
                & v13_waybel_0(X1,X0)
                & v2_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) ) ) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
            | ~ v1_waybel_7(X1,k7_lattice3(sK2))
            | ~ v12_waybel_0(X1,k7_lattice3(sK2))
            | ~ v1_waybel_0(X1,k7_lattice3(sK2))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v2_waybel_7(X1,sK2)
            | ~ v13_waybel_0(X1,sK2)
            | ~ v2_waybel_0(X1,sK2)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
              & v1_waybel_7(X1,k7_lattice3(sK2))
              & v12_waybel_0(X1,k7_lattice3(sK2))
              & v1_waybel_0(X1,k7_lattice3(sK2))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
              & v2_waybel_7(X1,sK2)
              & v13_waybel_0(X1,sK2)
              & v2_waybel_0(X1,sK2)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
      | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
      | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
      | ~ v1_waybel_0(sK3,k7_lattice3(sK2))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_waybel_7(sK3,sK2)
      | ~ v13_waybel_0(sK3,sK2)
      | ~ v2_waybel_0(sK3,sK2)
      | v1_xboole_0(sK3) )
    & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
        & v1_waybel_7(sK3,k7_lattice3(sK2))
        & v12_waybel_0(sK3,k7_lattice3(sK2))
        & v1_waybel_0(sK3,k7_lattice3(sK2))
        & ~ v1_xboole_0(sK3) )
      | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        & v2_waybel_7(sK3,sK2)
        & v13_waybel_0(sK3,sK2)
        & v2_waybel_0(sK3,sK2)
        & ~ v1_xboole_0(sK3) ) )
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).

fof(f82,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v2_waybel_7(X2,X0)
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_7(X2,X1)
                  & v13_waybel_0(X2,X1)
                  & v2_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_7(X2,X1)
                & v13_waybel_0(X2,X1)
                & v2_waybel_0(X2,X1)
                & ~ v1_xboole_0(X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X2,X0)
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1)
          | ~ v2_lattice3(X1)
          | ~ v1_lattice3(X1)
          | ~ v5_orders_2(X1)
          | ~ v4_orders_2(X1)
          | ~ v3_orders_2(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_7(X2,X1)
                & v13_waybel_0(X2,X1)
                & v2_waybel_0(X2,X1)
                & ~ v1_xboole_0(X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X2,X0)
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1)
          | ~ v2_lattice3(X1)
          | ~ v1_lattice3(X1)
          | ~ v5_orders_2(X1)
          | ~ v4_orders_2(X1)
          | ~ v3_orders_2(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_7(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(X1,X0)
        & v12_waybel_0(X1,X0)
        & v1_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f29,f34,f33])).

fof(f75,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ sP0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ sP0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(X1,X0)
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X1,X0)
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(X1,X0)
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X1,X0)
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,k7_lattice3(X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_7(X1,k7_lattice3(X0))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_7(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_58,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3247,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(subtyping,[status(esa)],[c_58])).

cnf(c_4166,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3247])).

cnf(c_1,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3259,plain,
    ( ~ l1_orders_2(X0_53)
    | l1_orders_2(k7_lattice3(X0_53)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4154,plain,
    ( l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(k7_lattice3(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3259])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | v1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_671,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | k7_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_672,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(k7_lattice3(X0))
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_676,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_1])).

cnf(c_3241,plain,
    ( ~ l1_orders_2(X0_53)
    | g1_orders_2(u1_struct_0(k7_lattice3(X0_53)),u1_orders_2(k7_lattice3(X0_53))) = k7_lattice3(X0_53) ),
    inference(subtyping,[status(esa)],[c_676])).

cnf(c_4172,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X0_53)),u1_orders_2(k7_lattice3(X0_53))) = k7_lattice3(X0_53)
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3241])).

cnf(c_5875,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(X0_53))),u1_orders_2(k7_lattice3(k7_lattice3(X0_53)))) = k7_lattice3(k7_lattice3(X0_53))
    | l1_orders_2(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_4154,c_4172])).

cnf(c_6561,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2)))) = k7_lattice3(k7_lattice3(sK2)) ),
    inference(superposition,[status(thm)],[c_4166,c_5875])).

cnf(c_13,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_57,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_361,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37,c_57])).

cnf(c_1560,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_lattice3(X2)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_361])).

cnf(c_1561,plain,
    ( ~ v2_waybel_0(sK3,X0)
    | ~ v13_waybel_0(sK3,X0)
    | ~ v2_waybel_7(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X0)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(unflattening,[status(thm)],[c_1560])).

cnf(c_3219,plain,
    ( ~ v2_waybel_0(sK3,X0_53)
    | ~ v13_waybel_0(sK3,X0_53)
    | ~ v2_waybel_7(sK3,X0_53)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ v2_lattice3(X1_53)
    | ~ v2_lattice3(X0_53)
    | ~ v1_lattice3(X1_53)
    | ~ v1_lattice3(X0_53)
    | ~ v5_orders_2(X1_53)
    | ~ v5_orders_2(X0_53)
    | ~ v4_orders_2(X1_53)
    | ~ v4_orders_2(X0_53)
    | ~ v3_orders_2(X1_53)
    | ~ v3_orders_2(X0_53)
    | ~ l1_orders_2(X1_53)
    | ~ l1_orders_2(X0_53)
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53)) ),
    inference(subtyping,[status(esa)],[c_1561])).

cnf(c_4194,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(X1_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(X1_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(X1_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(X1_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(X1_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3219])).

cnf(c_6582,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) = iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_4194])).

cnf(c_7002,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6582])).

cnf(c_14,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | v2_waybel_7(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1502,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | v2_waybel_7(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_lattice3(X2)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_361])).

cnf(c_1503,plain,
    ( ~ v2_waybel_0(sK3,X0)
    | ~ v13_waybel_0(sK3,X0)
    | ~ v2_waybel_7(sK3,X0)
    | v2_waybel_7(sK3,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X0)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(unflattening,[status(thm)],[c_1502])).

cnf(c_3220,plain,
    ( ~ v2_waybel_0(sK3,X0_53)
    | ~ v13_waybel_0(sK3,X0_53)
    | ~ v2_waybel_7(sK3,X0_53)
    | v2_waybel_7(sK3,X1_53)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ v2_lattice3(X1_53)
    | ~ v2_lattice3(X0_53)
    | ~ v1_lattice3(X1_53)
    | ~ v1_lattice3(X0_53)
    | ~ v5_orders_2(X1_53)
    | ~ v5_orders_2(X0_53)
    | ~ v4_orders_2(X1_53)
    | ~ v4_orders_2(X0_53)
    | ~ v3_orders_2(X1_53)
    | ~ v3_orders_2(X0_53)
    | ~ l1_orders_2(X1_53)
    | ~ l1_orders_2(X0_53)
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53)) ),
    inference(subtyping,[status(esa)],[c_1503])).

cnf(c_4193,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X1_53) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(X1_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(X1_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(X1_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(X1_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(X1_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3220])).

cnf(c_6579,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_7(sK3,X0_53) = iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_4193])).

cnf(c_6993,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_7(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6579])).

cnf(c_6578,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_4194])).

cnf(c_6990,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6578])).

cnf(c_31,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3252,plain,
    ( ~ l1_orders_2(X0_53)
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) = k7_lattice3(k7_lattice3(X0_53)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_4161,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) = k7_lattice3(k7_lattice3(X0_53))
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3252])).

cnf(c_4688,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = k7_lattice3(k7_lattice3(sK2)) ),
    inference(superposition,[status(thm)],[c_4166,c_4161])).

cnf(c_16,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(X0,X2)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1386,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(X0,X2)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_lattice3(X2)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_361])).

cnf(c_1387,plain,
    ( ~ v2_waybel_0(sK3,X0)
    | v2_waybel_0(sK3,X1)
    | ~ v13_waybel_0(sK3,X0)
    | ~ v2_waybel_7(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X0)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(unflattening,[status(thm)],[c_1386])).

cnf(c_3222,plain,
    ( ~ v2_waybel_0(sK3,X0_53)
    | v2_waybel_0(sK3,X1_53)
    | ~ v13_waybel_0(sK3,X0_53)
    | ~ v2_waybel_7(sK3,X0_53)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ v2_lattice3(X1_53)
    | ~ v2_lattice3(X0_53)
    | ~ v1_lattice3(X1_53)
    | ~ v1_lattice3(X0_53)
    | ~ v5_orders_2(X1_53)
    | ~ v5_orders_2(X0_53)
    | ~ v4_orders_2(X1_53)
    | ~ v4_orders_2(X0_53)
    | ~ v3_orders_2(X1_53)
    | ~ v3_orders_2(X0_53)
    | ~ l1_orders_2(X1_53)
    | ~ l1_orders_2(X0_53)
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53)) ),
    inference(subtyping,[status(esa)],[c_1387])).

cnf(c_4191,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_0(sK3,X1_53) = iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(X1_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(X1_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(X1_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(X1_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(X1_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3222])).

cnf(c_4900,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) = iProver_top
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_4191])).

cnf(c_63,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_64,plain,
    ( v3_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_65,plain,
    ( v4_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_66,plain,
    ( v5_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_67,plain,
    ( v1_lattice3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_59,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_68,plain,
    ( v2_lattice3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_69,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_5365,plain,
    ( l1_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) = iProver_top
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4900,c_64,c_65,c_66,c_67,c_68,c_69])).

cnf(c_5366,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) = iProver_top
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5365])).

cnf(c_6577,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_5366])).

cnf(c_4901,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_0(sK3,sK2) = iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_4191])).

cnf(c_5652,plain,
    ( l1_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_0(sK3,sK2) = iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4901,c_64,c_65,c_66,c_67,c_68,c_69])).

cnf(c_5653,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_0(sK3,sK2) = iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5652])).

cnf(c_6576,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_0(sK3,sK2) = iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_5653])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X0,X2)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1444,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X0,X2)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_lattice3(X2)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X2)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_361])).

cnf(c_1445,plain,
    ( ~ v2_waybel_0(sK3,X0)
    | ~ v13_waybel_0(sK3,X0)
    | v13_waybel_0(sK3,X1)
    | ~ v2_waybel_7(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_lattice3(X1)
    | ~ v2_lattice3(X0)
    | ~ v1_lattice3(X1)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(unflattening,[status(thm)],[c_1444])).

cnf(c_3221,plain,
    ( ~ v2_waybel_0(sK3,X0_53)
    | ~ v13_waybel_0(sK3,X0_53)
    | v13_waybel_0(sK3,X1_53)
    | ~ v2_waybel_7(sK3,X0_53)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ v2_lattice3(X1_53)
    | ~ v2_lattice3(X0_53)
    | ~ v1_lattice3(X1_53)
    | ~ v1_lattice3(X0_53)
    | ~ v5_orders_2(X1_53)
    | ~ v5_orders_2(X0_53)
    | ~ v4_orders_2(X1_53)
    | ~ v4_orders_2(X0_53)
    | ~ v3_orders_2(X1_53)
    | ~ v3_orders_2(X0_53)
    | ~ l1_orders_2(X1_53)
    | ~ l1_orders_2(X0_53)
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53)) ),
    inference(subtyping,[status(esa)],[c_1445])).

cnf(c_4192,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != g1_orders_2(u1_struct_0(X1_53),u1_orders_2(X1_53))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X1_53) = iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(X1_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(X1_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(X1_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(X1_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(X1_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3221])).

cnf(c_4996,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,X0_53) = iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_4192])).

cnf(c_5723,plain,
    ( l1_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,X0_53) = iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4996,c_64,c_65,c_66,c_67,c_68,c_69])).

cnf(c_5724,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,X0_53) = iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5723])).

cnf(c_6575,plain,
    ( v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_5724])).

cnf(c_4997,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,sK2) = iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_4192])).

cnf(c_5742,plain,
    ( l1_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,sK2) = iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4997,c_64,c_65,c_66,c_67,c_68,c_69])).

cnf(c_5743,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,X0_53) != iProver_top
    | v13_waybel_0(sK3,sK2) = iProver_top
    | v2_waybel_7(sK3,X0_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5742])).

cnf(c_6574,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v13_waybel_0(sK3,sK2) = iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_5743])).

cnf(c_5145,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,X0_53) = iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v2_lattice3(sK2) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v1_lattice3(sK2) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_4193])).

cnf(c_5853,plain,
    ( l1_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,X0_53) = iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5145,c_64,c_65,c_66,c_67,c_68,c_69])).

cnf(c_5854,plain,
    ( g1_orders_2(u1_struct_0(X0_53),u1_orders_2(X0_53)) != k7_lattice3(k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,X0_53) = iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5853])).

cnf(c_6573,plain,
    ( v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v5_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v4_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v3_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(k7_lattice3(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6561,c_5854])).

cnf(c_5674,plain,
    ( l1_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ l1_orders_2(k7_lattice3(sK2)) ),
    inference(instantiation,[status(thm)],[c_3259])).

cnf(c_5675,plain,
    ( l1_orders_2(k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5674])).

cnf(c_30,plain,
    ( sP1(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3253,plain,
    ( sP1(X0_53)
    | ~ v2_lattice3(X0_53)
    | ~ v1_lattice3(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ v4_orders_2(X0_53)
    | ~ v3_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_4160,plain,
    ( sP1(X0_53) = iProver_top
    | v2_lattice3(X0_53) != iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | v4_orders_2(X0_53) != iProver_top
    | v3_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3253])).

cnf(c_5538,plain,
    ( sP1(k7_lattice3(X0_53)) = iProver_top
    | v2_lattice3(k7_lattice3(X0_53)) != iProver_top
    | v1_lattice3(k7_lattice3(X0_53)) != iProver_top
    | v5_orders_2(k7_lattice3(X0_53)) != iProver_top
    | v4_orders_2(k7_lattice3(X0_53)) != iProver_top
    | v3_orders_2(k7_lattice3(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_4154,c_4160])).

cnf(c_5567,plain,
    ( sP1(k7_lattice3(sK2)) = iProver_top
    | v2_lattice3(k7_lattice3(sK2)) != iProver_top
    | v1_lattice3(k7_lattice3(sK2)) != iProver_top
    | v5_orders_2(k7_lattice3(sK2)) != iProver_top
    | v4_orders_2(k7_lattice3(sK2)) != iProver_top
    | v3_orders_2(k7_lattice3(sK2)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5538])).

cnf(c_3,plain,
    ( ~ v3_orders_2(X0)
    | v3_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3258,plain,
    ( ~ v3_orders_2(X0_53)
    | v3_orders_2(k7_lattice3(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5392,plain,
    ( v3_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ v3_orders_2(k7_lattice3(sK2))
    | ~ l1_orders_2(k7_lattice3(sK2)) ),
    inference(instantiation,[status(thm)],[c_3258])).

cnf(c_5393,plain,
    ( v3_orders_2(k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v3_orders_2(k7_lattice3(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5392])).

cnf(c_5,plain,
    ( ~ v4_orders_2(X0)
    | v4_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3257,plain,
    ( ~ v4_orders_2(X0_53)
    | v4_orders_2(k7_lattice3(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5323,plain,
    ( v4_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ v4_orders_2(k7_lattice3(sK2))
    | ~ l1_orders_2(k7_lattice3(sK2)) ),
    inference(instantiation,[status(thm)],[c_3257])).

cnf(c_5324,plain,
    ( v4_orders_2(k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v4_orders_2(k7_lattice3(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5323])).

cnf(c_7,plain,
    ( ~ v5_orders_2(X0)
    | v5_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3256,plain,
    ( ~ v5_orders_2(X0_53)
    | v5_orders_2(k7_lattice3(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_4863,plain,
    ( v5_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ v5_orders_2(k7_lattice3(sK2))
    | ~ l1_orders_2(k7_lattice3(sK2)) ),
    inference(instantiation,[status(thm)],[c_3256])).

cnf(c_4864,plain,
    ( v5_orders_2(k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v5_orders_2(k7_lattice3(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4863])).

cnf(c_9,plain,
    ( ~ v2_lattice3(X0)
    | v1_lattice3(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3255,plain,
    ( ~ v2_lattice3(X0_53)
    | v1_lattice3(k7_lattice3(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4749,plain,
    ( ~ v2_lattice3(k7_lattice3(sK2))
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2)))
    | ~ l1_orders_2(k7_lattice3(sK2)) ),
    inference(instantiation,[status(thm)],[c_3255])).

cnf(c_4750,plain,
    ( v2_lattice3(k7_lattice3(sK2)) != iProver_top
    | v1_lattice3(k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4749])).

cnf(c_11,plain,
    ( v2_lattice3(k7_lattice3(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3254,plain,
    ( v2_lattice3(k7_lattice3(X0_53))
    | ~ v1_lattice3(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4720,plain,
    ( v2_lattice3(k7_lattice3(k7_lattice3(sK2)))
    | ~ v1_lattice3(k7_lattice3(sK2))
    | ~ l1_orders_2(k7_lattice3(sK2)) ),
    inference(instantiation,[status(thm)],[c_3254])).

cnf(c_4721,plain,
    ( v2_lattice3(k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v1_lattice3(k7_lattice3(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4720])).

cnf(c_3325,plain,
    ( ~ l1_orders_2(sK2)
    | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = k7_lattice3(k7_lattice3(sK2)) ),
    inference(instantiation,[status(thm)],[c_3252])).

cnf(c_3318,plain,
    ( v2_lattice3(k7_lattice3(X0_53)) = iProver_top
    | v1_lattice3(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3254])).

cnf(c_3320,plain,
    ( v2_lattice3(k7_lattice3(sK2)) = iProver_top
    | v1_lattice3(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3318])).

cnf(c_3315,plain,
    ( v2_lattice3(X0_53) != iProver_top
    | v1_lattice3(k7_lattice3(X0_53)) = iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3255])).

cnf(c_3317,plain,
    ( v2_lattice3(sK2) != iProver_top
    | v1_lattice3(k7_lattice3(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3315])).

cnf(c_3312,plain,
    ( v5_orders_2(X0_53) != iProver_top
    | v5_orders_2(k7_lattice3(X0_53)) = iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3256])).

cnf(c_3314,plain,
    ( v5_orders_2(k7_lattice3(sK2)) = iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3312])).

cnf(c_3309,plain,
    ( v4_orders_2(X0_53) != iProver_top
    | v4_orders_2(k7_lattice3(X0_53)) = iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3257])).

cnf(c_3311,plain,
    ( v4_orders_2(k7_lattice3(sK2)) = iProver_top
    | v4_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3309])).

cnf(c_3306,plain,
    ( v3_orders_2(X0_53) != iProver_top
    | v3_orders_2(k7_lattice3(X0_53)) = iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3258])).

cnf(c_3308,plain,
    ( v3_orders_2(k7_lattice3(sK2)) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3306])).

cnf(c_3303,plain,
    ( l1_orders_2(X0_53) != iProver_top
    | l1_orders_2(k7_lattice3(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3259])).

cnf(c_3305,plain,
    ( l1_orders_2(k7_lattice3(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3303])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
    | ~ sP1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ v1_waybel_7(X0,X1)
    | sP0(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,negated_conjecture,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_912,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | sP0(X1,X0)
    | v2_waybel_0(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_41])).

cnf(c_913,plain,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | sP0(k7_lattice3(sK2),sK3)
    | v2_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_51,negated_conjecture,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_46,negated_conjecture,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_36,negated_conjecture,
    ( v2_waybel_0(sK3,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_915,plain,
    ( sP0(k7_lattice3(sK2),sK3)
    | v2_waybel_0(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_57,c_51,c_46,c_36])).

cnf(c_1267,plain,
    ( v2_waybel_0(sK3,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_915])).

cnf(c_1268,plain,
    ( v2_waybel_0(sK3,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1267])).

cnf(c_1269,plain,
    ( v2_waybel_0(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_40,negated_conjecture,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_926,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | sP0(X1,X0)
    | v13_waybel_0(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_40])).

cnf(c_927,plain,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | sP0(k7_lattice3(sK2),sK3)
    | v13_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_50,negated_conjecture,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_45,negated_conjecture,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_35,negated_conjecture,
    ( v13_waybel_0(sK3,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_929,plain,
    ( sP0(k7_lattice3(sK2),sK3)
    | v13_waybel_0(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_57,c_50,c_45,c_35])).

cnf(c_1254,plain,
    ( v13_waybel_0(sK3,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_929])).

cnf(c_1255,plain,
    ( v13_waybel_0(sK3,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1254])).

cnf(c_1256,plain,
    ( v13_waybel_0(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_39,negated_conjecture,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_940,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | sP0(X1,X0)
    | v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_941,plain,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | sP0(k7_lattice3(sK2),sK3)
    | v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_940])).

cnf(c_49,negated_conjecture,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,negated_conjecture,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_34,negated_conjecture,
    ( v2_waybel_7(sK3,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2)))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_943,plain,
    ( sP0(k7_lattice3(sK2),sK3)
    | v2_waybel_7(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_57,c_49,c_44,c_34])).

cnf(c_1241,plain,
    ( v2_waybel_7(sK3,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_943])).

cnf(c_1242,plain,
    ( v2_waybel_7(sK3,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1241])).

cnf(c_1243,plain,
    ( v2_waybel_7(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_38,negated_conjecture,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_954,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | sP0(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_955,plain,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | sP0(k7_lattice3(sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_48,negated_conjecture,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_43,negated_conjecture,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_957,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | sP0(k7_lattice3(sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_57,c_48,c_43,c_33])).

cnf(c_958,plain,
    ( sP0(k7_lattice3(sK2),sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_957])).

cnf(c_1228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_958])).

cnf(c_1229,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1228])).

cnf(c_1230,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1229])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | v2_waybel_7(X1,k7_lattice3(X0))
    | ~ sP1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1215,plain,
    ( v2_waybel_0(sK3,sK2)
    | v2_waybel_7(X0,k7_lattice3(X1))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_915])).

cnf(c_1216,plain,
    ( v2_waybel_0(sK3,sK2)
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1215])).

cnf(c_1217,plain,
    ( v2_waybel_0(sK3,sK2) = iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_1202,plain,
    ( v13_waybel_0(sK3,sK2)
    | v2_waybel_7(X0,k7_lattice3(X1))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_929])).

cnf(c_1203,plain,
    ( v13_waybel_0(sK3,sK2)
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1202])).

cnf(c_1204,plain,
    ( v13_waybel_0(sK3,sK2) = iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1203])).

cnf(c_1189,plain,
    ( v2_waybel_7(X0,k7_lattice3(X1))
    | v2_waybel_7(sK3,sK2)
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_943])).

cnf(c_1190,plain,
    ( v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | v2_waybel_7(sK3,sK2)
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1189])).

cnf(c_1191,plain,
    ( v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v2_waybel_7(sK3,sK2) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_1176,plain,
    ( v2_waybel_7(X0,k7_lattice3(X1))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_958])).

cnf(c_1177,plain,
    ( v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1176])).

cnf(c_1178,plain,
    ( v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1177])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1)
    | v13_waybel_0(X1,k7_lattice3(X0))
    | ~ sP1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1163,plain,
    ( v2_waybel_0(sK3,sK2)
    | v13_waybel_0(X0,k7_lattice3(X1))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_915])).

cnf(c_1164,plain,
    ( v2_waybel_0(sK3,sK2)
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1163])).

cnf(c_1165,plain,
    ( v2_waybel_0(sK3,sK2) = iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1164])).

cnf(c_1150,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | v13_waybel_0(sK3,sK2)
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_929])).

cnf(c_1151,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | v13_waybel_0(sK3,sK2)
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1150])).

cnf(c_1152,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v13_waybel_0(sK3,sK2) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_1137,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | v2_waybel_7(sK3,sK2)
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_943])).

cnf(c_1138,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | v2_waybel_7(sK3,sK2)
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1137])).

cnf(c_1139,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v2_waybel_7(sK3,sK2) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_1124,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_958])).

cnf(c_1125,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1124])).

cnf(c_1126,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1)
    | v2_waybel_0(X1,k7_lattice3(X0))
    | ~ sP1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1111,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | v2_waybel_0(sK3,sK2)
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_915])).

cnf(c_1112,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | v2_waybel_0(sK3,sK2)
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1111])).

cnf(c_1113,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v2_waybel_0(sK3,sK2) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1112])).

cnf(c_1098,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | v13_waybel_0(sK3,sK2)
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_929])).

cnf(c_1099,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | v13_waybel_0(sK3,sK2)
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1098])).

cnf(c_1100,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v13_waybel_0(sK3,sK2) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_1085,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | v2_waybel_7(sK3,sK2)
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_943])).

cnf(c_1086,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | v2_waybel_7(sK3,sK2)
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1085])).

cnf(c_1087,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | v2_waybel_7(sK3,sK2) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_1072,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(X1)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_958])).

cnf(c_1073,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(k7_lattice3(sK2)) ),
    inference(unflattening,[status(thm)],[c_1072])).

cnf(c_1074,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1073])).

cnf(c_18,plain,
    ( sP0(X0,X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X0))
    | ~ v13_waybel_0(X1,k7_lattice3(X0))
    | ~ v2_waybel_7(X1,k7_lattice3(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
    | ~ sP1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,plain,
    ( v1_waybel_7(X0,X1)
    | ~ sP0(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_370,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ v2_waybel_7(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v1_waybel_0(sK3,k7_lattice3(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_57])).

cnf(c_371,negated_conjecture,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_886,plain,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ sP0(X0,X1)
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_lattice3(sK2) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_371])).

cnf(c_887,plain,
    ( ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ sP0(k7_lattice3(sK2),sK3)
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,plain,
    ( v12_waybel_0(X0,X1)
    | ~ sP0(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,plain,
    ( v1_waybel_0(X0,X1)
    | ~ sP0(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_905,plain,
    ( ~ sP0(k7_lattice3(sK2),sK3)
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_887,c_25,c_27,c_28])).

cnf(c_1021,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_7(X0,k7_lattice3(X1))
    | ~ v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(X1)
    | v1_xboole_0(X0)
    | k7_lattice3(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_905])).

cnf(c_1022,plain,
    ( ~ v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ v2_waybel_0(sK3,sK2)
    | ~ v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ v2_waybel_7(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP1(k7_lattice3(sK2))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1021])).

cnf(c_1023,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_0(sK3,sK2) != iProver_top
    | v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v13_waybel_0(sK3,sK2) != iProver_top
    | v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) != iProver_top
    | v2_waybel_7(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP1(k7_lattice3(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_70,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7002,c_6993,c_6990,c_6577,c_6576,c_6575,c_6574,c_6573,c_5675,c_5567,c_5393,c_5324,c_4864,c_4750,c_4721,c_3325,c_3320,c_3317,c_3314,c_3311,c_3308,c_3305,c_1269,c_1256,c_1243,c_1230,c_1217,c_1204,c_1191,c_1178,c_1165,c_1152,c_1139,c_1126,c_1113,c_1100,c_1087,c_1074,c_1023,c_70,c_69,c_58,c_68,c_67,c_66,c_65,c_64])).


%------------------------------------------------------------------------------
