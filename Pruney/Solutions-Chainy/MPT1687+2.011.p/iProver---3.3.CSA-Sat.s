%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:14 EST 2020

% Result     : CounterSatisfiable 1.64s
% Output     : Saturation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  166 (1516 expanded)
%              Number of clauses        :  111 ( 484 expanded)
%              Number of leaves         :   25 ( 397 expanded)
%              Depth                    :   16
%              Number of atoms          :  514 (11115 expanded)
%              Number of equality atoms :  252 (1922 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                    & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
            | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_funct_1(X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(X0)
          | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(k2_funct_1(sK2)) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
              | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
              | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(X0))
              | ~ v1_funct_1(k2_funct_1(X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                  | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(k2_funct_1(X2)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37,f36])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_244,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_242,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_241,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_239,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_232,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_229,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_443,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_444,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_699,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k1_relset_1(X0_52,X1_52,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_444])).

cnf(c_844,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_699])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_399,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_650,plain,
    ( k1_relset_1(X0,X1,sK2) = X0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_399])).

cnf(c_651,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_694,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_953,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_844,c_694])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_269,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_287,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_288,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_371,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_269,c_288])).

cnf(c_372,plain,
    ( v2_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_374,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_21])).

cnf(c_703,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_993,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_953,c_703])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_5,c_4,c_3])).

cnf(c_389,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_17])).

cnf(c_390,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_701,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k7_relat_1(sK2,X0_52) = sK2 ),
    inference(subtyping,[status(esa)],[c_390])).

cnf(c_841,plain,
    ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_701])).

cnf(c_999,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_993,c_841])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_452,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_453,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_595,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_453])).

cnf(c_596,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_697,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k2_relat_1(k7_relat_1(sK2,X2_52)) = k9_relat_1(sK2,X2_52) ),
    inference(subtyping,[status(esa)],[c_596])).

cnf(c_704,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_52)) = k9_relat_1(sK2,X0_52)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_697])).

cnf(c_778,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_52)) = k9_relat_1(sK2,X0_52)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_706,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_697])).

cnf(c_709,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_845,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_705,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_697])).

cnf(c_846,plain,
    ( ~ sP1_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1318,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_52)) = k9_relat_1(sK2,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_778,c_706,c_704,c_845,c_846])).

cnf(c_1322,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_999,c_1318])).

cnf(c_776,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_742,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_848,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_1312,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_742,c_845,c_848])).

cnf(c_777,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_1267,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_777,c_845,c_848])).

cnf(c_1004,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k7_relat_1(sK2,X0_52) = sK2 ),
    inference(demodulation,[status(thm)],[c_993,c_701])).

cnf(c_1003,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k1_relset_1(X0_52,X1_52,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_993,c_699])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_434,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_435,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_700,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k2_relset_1(X0_52,X1_52,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_1002,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k2_relset_1(X0_52,X1_52,sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_993,c_700])).

cnf(c_16,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_325,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_funct_1(sK2) != sK2
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_529,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | k2_funct_1(sK2) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_325,c_17])).

cnf(c_618,plain,
    ( k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_529,c_18])).

cnf(c_696,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_1001,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_993,c_696])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_294,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_295,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_379,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_269,c_295])).

cnf(c_380,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_382,plain,
    ( u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_380,c_23])).

cnf(c_702,plain,
    ( u1_struct_0(sK0) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1000,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_993,c_702])).

cnf(c_11,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_416,plain,
    ( v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_417,plain,
    ( v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_631,plain,
    ( k1_relset_1(X0,X1,sK2) != X0
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != X0
    | u1_struct_0(sK0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_417])).

cnf(c_632,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_funct_1(sK2) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_695,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_632])).

cnf(c_711,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_865,plain,
    ( u1_struct_0(sK0) != X0_52
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != X0_52 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_878,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_707,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_879,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_908,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_funct_1(sK2) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_702,c_878,c_879])).

cnf(c_909,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_908])).

cnf(c_998,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_993,c_909])).

cnf(c_997,plain,
    ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_993,c_844])).

cnf(c_860,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_700])).

cnf(c_996,plain,
    ( k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_993,c_860])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_586,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_453])).

cnf(c_587,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_698,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
    | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_587])).

cnf(c_847,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_914,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_845,c_847])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:09:04 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 1.64/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.01  
% 1.64/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.64/1.01  
% 1.64/1.01  ------  iProver source info
% 1.64/1.01  
% 1.64/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.64/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.64/1.01  git: non_committed_changes: false
% 1.64/1.01  git: last_make_outside_of_git: false
% 1.64/1.01  
% 1.64/1.01  ------ 
% 1.64/1.01  
% 1.64/1.01  ------ Input Options
% 1.64/1.01  
% 1.64/1.01  --out_options                           all
% 1.64/1.01  --tptp_safe_out                         true
% 1.64/1.01  --problem_path                          ""
% 1.64/1.01  --include_path                          ""
% 1.64/1.01  --clausifier                            res/vclausify_rel
% 1.64/1.01  --clausifier_options                    --mode clausify
% 1.64/1.01  --stdin                                 false
% 1.64/1.01  --stats_out                             all
% 1.64/1.01  
% 1.64/1.01  ------ General Options
% 1.64/1.01  
% 1.64/1.01  --fof                                   false
% 1.64/1.01  --time_out_real                         305.
% 1.64/1.01  --time_out_virtual                      -1.
% 1.64/1.01  --symbol_type_check                     false
% 1.64/1.01  --clausify_out                          false
% 1.64/1.01  --sig_cnt_out                           false
% 1.64/1.01  --trig_cnt_out                          false
% 1.64/1.01  --trig_cnt_out_tolerance                1.
% 1.64/1.01  --trig_cnt_out_sk_spl                   false
% 1.64/1.01  --abstr_cl_out                          false
% 1.64/1.01  
% 1.64/1.01  ------ Global Options
% 1.64/1.01  
% 1.64/1.01  --schedule                              default
% 1.64/1.01  --add_important_lit                     false
% 1.64/1.01  --prop_solver_per_cl                    1000
% 1.64/1.01  --min_unsat_core                        false
% 1.64/1.01  --soft_assumptions                      false
% 1.64/1.01  --soft_lemma_size                       3
% 1.64/1.01  --prop_impl_unit_size                   0
% 1.64/1.01  --prop_impl_unit                        []
% 1.64/1.01  --share_sel_clauses                     true
% 1.64/1.01  --reset_solvers                         false
% 1.64/1.01  --bc_imp_inh                            [conj_cone]
% 1.64/1.01  --conj_cone_tolerance                   3.
% 1.64/1.01  --extra_neg_conj                        none
% 1.64/1.01  --large_theory_mode                     true
% 1.64/1.01  --prolific_symb_bound                   200
% 1.64/1.01  --lt_threshold                          2000
% 1.64/1.01  --clause_weak_htbl                      true
% 1.64/1.01  --gc_record_bc_elim                     false
% 1.64/1.01  
% 1.64/1.01  ------ Preprocessing Options
% 1.64/1.01  
% 1.64/1.01  --preprocessing_flag                    true
% 1.64/1.01  --time_out_prep_mult                    0.1
% 1.64/1.01  --splitting_mode                        input
% 1.64/1.01  --splitting_grd                         true
% 1.64/1.01  --splitting_cvd                         false
% 1.64/1.01  --splitting_cvd_svl                     false
% 1.64/1.01  --splitting_nvd                         32
% 1.64/1.01  --sub_typing                            true
% 1.64/1.01  --prep_gs_sim                           true
% 1.64/1.01  --prep_unflatten                        true
% 1.64/1.01  --prep_res_sim                          true
% 1.64/1.01  --prep_upred                            true
% 1.64/1.01  --prep_sem_filter                       exhaustive
% 1.64/1.01  --prep_sem_filter_out                   false
% 1.64/1.01  --pred_elim                             true
% 1.64/1.01  --res_sim_input                         true
% 1.64/1.01  --eq_ax_congr_red                       true
% 1.64/1.01  --pure_diseq_elim                       true
% 1.64/1.01  --brand_transform                       false
% 1.64/1.01  --non_eq_to_eq                          false
% 1.64/1.01  --prep_def_merge                        true
% 1.64/1.01  --prep_def_merge_prop_impl              false
% 1.64/1.01  --prep_def_merge_mbd                    true
% 1.64/1.01  --prep_def_merge_tr_red                 false
% 1.64/1.01  --prep_def_merge_tr_cl                  false
% 1.64/1.01  --smt_preprocessing                     true
% 1.64/1.01  --smt_ac_axioms                         fast
% 1.64/1.01  --preprocessed_out                      false
% 1.64/1.01  --preprocessed_stats                    false
% 1.64/1.01  
% 1.64/1.01  ------ Abstraction refinement Options
% 1.64/1.01  
% 1.64/1.01  --abstr_ref                             []
% 1.64/1.01  --abstr_ref_prep                        false
% 1.64/1.01  --abstr_ref_until_sat                   false
% 1.64/1.01  --abstr_ref_sig_restrict                funpre
% 1.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/1.01  --abstr_ref_under                       []
% 1.64/1.01  
% 1.64/1.01  ------ SAT Options
% 1.64/1.01  
% 1.64/1.01  --sat_mode                              false
% 1.64/1.01  --sat_fm_restart_options                ""
% 1.64/1.01  --sat_gr_def                            false
% 1.64/1.01  --sat_epr_types                         true
% 1.64/1.01  --sat_non_cyclic_types                  false
% 1.64/1.01  --sat_finite_models                     false
% 1.64/1.01  --sat_fm_lemmas                         false
% 1.64/1.01  --sat_fm_prep                           false
% 1.64/1.01  --sat_fm_uc_incr                        true
% 1.64/1.01  --sat_out_model                         small
% 1.64/1.01  --sat_out_clauses                       false
% 1.64/1.01  
% 1.64/1.01  ------ QBF Options
% 1.64/1.01  
% 1.64/1.01  --qbf_mode                              false
% 1.64/1.01  --qbf_elim_univ                         false
% 1.64/1.01  --qbf_dom_inst                          none
% 1.64/1.01  --qbf_dom_pre_inst                      false
% 1.64/1.01  --qbf_sk_in                             false
% 1.64/1.01  --qbf_pred_elim                         true
% 1.64/1.01  --qbf_split                             512
% 1.64/1.01  
% 1.64/1.01  ------ BMC1 Options
% 1.64/1.01  
% 1.64/1.01  --bmc1_incremental                      false
% 1.64/1.01  --bmc1_axioms                           reachable_all
% 1.64/1.01  --bmc1_min_bound                        0
% 1.64/1.01  --bmc1_max_bound                        -1
% 1.64/1.01  --bmc1_max_bound_default                -1
% 1.64/1.01  --bmc1_symbol_reachability              true
% 1.64/1.01  --bmc1_property_lemmas                  false
% 1.64/1.01  --bmc1_k_induction                      false
% 1.64/1.01  --bmc1_non_equiv_states                 false
% 1.64/1.01  --bmc1_deadlock                         false
% 1.64/1.01  --bmc1_ucm                              false
% 1.64/1.01  --bmc1_add_unsat_core                   none
% 1.64/1.01  --bmc1_unsat_core_children              false
% 1.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/1.01  --bmc1_out_stat                         full
% 1.64/1.01  --bmc1_ground_init                      false
% 1.64/1.01  --bmc1_pre_inst_next_state              false
% 1.64/1.01  --bmc1_pre_inst_state                   false
% 1.64/1.01  --bmc1_pre_inst_reach_state             false
% 1.64/1.01  --bmc1_out_unsat_core                   false
% 1.64/1.01  --bmc1_aig_witness_out                  false
% 1.64/1.01  --bmc1_verbose                          false
% 1.64/1.01  --bmc1_dump_clauses_tptp                false
% 1.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.64/1.01  --bmc1_dump_file                        -
% 1.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.64/1.01  --bmc1_ucm_extend_mode                  1
% 1.64/1.01  --bmc1_ucm_init_mode                    2
% 1.64/1.01  --bmc1_ucm_cone_mode                    none
% 1.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.64/1.01  --bmc1_ucm_relax_model                  4
% 1.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/1.01  --bmc1_ucm_layered_model                none
% 1.64/1.01  --bmc1_ucm_max_lemma_size               10
% 1.64/1.01  
% 1.64/1.01  ------ AIG Options
% 1.64/1.01  
% 1.64/1.01  --aig_mode                              false
% 1.64/1.01  
% 1.64/1.01  ------ Instantiation Options
% 1.64/1.01  
% 1.64/1.01  --instantiation_flag                    true
% 1.64/1.01  --inst_sos_flag                         false
% 1.64/1.01  --inst_sos_phase                        true
% 1.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/1.01  --inst_lit_sel_side                     num_symb
% 1.64/1.01  --inst_solver_per_active                1400
% 1.64/1.01  --inst_solver_calls_frac                1.
% 1.64/1.01  --inst_passive_queue_type               priority_queues
% 1.64/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.64/1.01  --inst_passive_queues_freq              [25;2]
% 1.64/1.01  --inst_dismatching                      true
% 1.64/1.01  --inst_eager_unprocessed_to_passive     true
% 1.64/1.01  --inst_prop_sim_given                   true
% 1.64/1.01  --inst_prop_sim_new                     false
% 1.64/1.01  --inst_subs_new                         false
% 1.64/1.01  --inst_eq_res_simp                      false
% 1.64/1.01  --inst_subs_given                       false
% 1.64/1.01  --inst_orphan_elimination               true
% 1.64/1.01  --inst_learning_loop_flag               true
% 1.64/1.01  --inst_learning_start                   3000
% 1.64/1.01  --inst_learning_factor                  2
% 1.64/1.01  --inst_start_prop_sim_after_learn       3
% 1.64/1.01  --inst_sel_renew                        solver
% 1.64/1.01  --inst_lit_activity_flag                true
% 1.64/1.01  --inst_restr_to_given                   false
% 1.64/1.01  --inst_activity_threshold               500
% 1.64/1.01  --inst_out_proof                        true
% 1.64/1.01  
% 1.64/1.01  ------ Resolution Options
% 1.64/1.01  
% 1.64/1.01  --resolution_flag                       true
% 1.64/1.01  --res_lit_sel                           adaptive
% 1.64/1.01  --res_lit_sel_side                      none
% 1.64/1.01  --res_ordering                          kbo
% 1.64/1.01  --res_to_prop_solver                    active
% 1.64/1.01  --res_prop_simpl_new                    false
% 1.64/1.01  --res_prop_simpl_given                  true
% 1.64/1.01  --res_passive_queue_type                priority_queues
% 1.64/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.64/1.01  --res_passive_queues_freq               [15;5]
% 1.64/1.01  --res_forward_subs                      full
% 1.64/1.01  --res_backward_subs                     full
% 1.64/1.01  --res_forward_subs_resolution           true
% 1.64/1.01  --res_backward_subs_resolution          true
% 1.64/1.01  --res_orphan_elimination                true
% 1.64/1.01  --res_time_limit                        2.
% 1.64/1.01  --res_out_proof                         true
% 1.64/1.01  
% 1.64/1.01  ------ Superposition Options
% 1.64/1.01  
% 1.64/1.01  --superposition_flag                    true
% 1.64/1.01  --sup_passive_queue_type                priority_queues
% 1.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.64/1.01  --demod_completeness_check              fast
% 1.64/1.01  --demod_use_ground                      true
% 1.64/1.01  --sup_to_prop_solver                    passive
% 1.64/1.01  --sup_prop_simpl_new                    true
% 1.64/1.01  --sup_prop_simpl_given                  true
% 1.64/1.01  --sup_fun_splitting                     false
% 1.64/1.01  --sup_smt_interval                      50000
% 1.64/1.01  
% 1.64/1.01  ------ Superposition Simplification Setup
% 1.64/1.01  
% 1.64/1.01  --sup_indices_passive                   []
% 1.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.01  --sup_full_bw                           [BwDemod]
% 1.64/1.01  --sup_immed_triv                        [TrivRules]
% 1.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.01  --sup_immed_bw_main                     []
% 1.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.01  
% 1.64/1.01  ------ Combination Options
% 1.64/1.01  
% 1.64/1.01  --comb_res_mult                         3
% 1.64/1.01  --comb_sup_mult                         2
% 1.64/1.01  --comb_inst_mult                        10
% 1.64/1.01  
% 1.64/1.01  ------ Debug Options
% 1.64/1.01  
% 1.64/1.01  --dbg_backtrace                         false
% 1.64/1.01  --dbg_dump_prop_clauses                 false
% 1.64/1.01  --dbg_dump_prop_clauses_file            -
% 1.64/1.01  --dbg_out_stat                          false
% 1.64/1.01  ------ Parsing...
% 1.64/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.64/1.01  
% 1.64/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.64/1.01  
% 1.64/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.64/1.01  
% 1.64/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.64/1.01  ------ Proving...
% 1.64/1.01  ------ Problem Properties 
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  clauses                                 12
% 1.64/1.01  conjectures                             0
% 1.64/1.01  EPR                                     1
% 1.64/1.01  Horn                                    10
% 1.64/1.01  unary                                   2
% 1.64/1.01  binary                                  8
% 1.64/1.01  lits                                    27
% 1.64/1.01  lits eq                                 23
% 1.64/1.01  fd_pure                                 0
% 1.64/1.01  fd_pseudo                               0
% 1.64/1.01  fd_cond                                 0
% 1.64/1.01  fd_pseudo_cond                          0
% 1.64/1.01  AC symbols                              0
% 1.64/1.01  
% 1.64/1.01  ------ Schedule dynamic 5 is on 
% 1.64/1.01  
% 1.64/1.01  ------ no conjectures: strip conj schedule 
% 1.64/1.01  
% 1.64/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  ------ 
% 1.64/1.01  Current options:
% 1.64/1.01  ------ 
% 1.64/1.01  
% 1.64/1.01  ------ Input Options
% 1.64/1.01  
% 1.64/1.01  --out_options                           all
% 1.64/1.01  --tptp_safe_out                         true
% 1.64/1.01  --problem_path                          ""
% 1.64/1.01  --include_path                          ""
% 1.64/1.01  --clausifier                            res/vclausify_rel
% 1.64/1.01  --clausifier_options                    --mode clausify
% 1.64/1.01  --stdin                                 false
% 1.64/1.01  --stats_out                             all
% 1.64/1.01  
% 1.64/1.01  ------ General Options
% 1.64/1.01  
% 1.64/1.01  --fof                                   false
% 1.64/1.01  --time_out_real                         305.
% 1.64/1.01  --time_out_virtual                      -1.
% 1.64/1.01  --symbol_type_check                     false
% 1.64/1.01  --clausify_out                          false
% 1.64/1.01  --sig_cnt_out                           false
% 1.64/1.01  --trig_cnt_out                          false
% 1.64/1.01  --trig_cnt_out_tolerance                1.
% 1.64/1.01  --trig_cnt_out_sk_spl                   false
% 1.64/1.01  --abstr_cl_out                          false
% 1.64/1.01  
% 1.64/1.01  ------ Global Options
% 1.64/1.01  
% 1.64/1.01  --schedule                              default
% 1.64/1.01  --add_important_lit                     false
% 1.64/1.01  --prop_solver_per_cl                    1000
% 1.64/1.01  --min_unsat_core                        false
% 1.64/1.01  --soft_assumptions                      false
% 1.64/1.01  --soft_lemma_size                       3
% 1.64/1.01  --prop_impl_unit_size                   0
% 1.64/1.01  --prop_impl_unit                        []
% 1.64/1.01  --share_sel_clauses                     true
% 1.64/1.01  --reset_solvers                         false
% 1.64/1.01  --bc_imp_inh                            [conj_cone]
% 1.64/1.01  --conj_cone_tolerance                   3.
% 1.64/1.01  --extra_neg_conj                        none
% 1.64/1.01  --large_theory_mode                     true
% 1.64/1.01  --prolific_symb_bound                   200
% 1.64/1.01  --lt_threshold                          2000
% 1.64/1.01  --clause_weak_htbl                      true
% 1.64/1.01  --gc_record_bc_elim                     false
% 1.64/1.01  
% 1.64/1.01  ------ Preprocessing Options
% 1.64/1.01  
% 1.64/1.01  --preprocessing_flag                    true
% 1.64/1.01  --time_out_prep_mult                    0.1
% 1.64/1.01  --splitting_mode                        input
% 1.64/1.01  --splitting_grd                         true
% 1.64/1.01  --splitting_cvd                         false
% 1.64/1.01  --splitting_cvd_svl                     false
% 1.64/1.01  --splitting_nvd                         32
% 1.64/1.01  --sub_typing                            true
% 1.64/1.01  --prep_gs_sim                           true
% 1.64/1.01  --prep_unflatten                        true
% 1.64/1.01  --prep_res_sim                          true
% 1.64/1.01  --prep_upred                            true
% 1.64/1.01  --prep_sem_filter                       exhaustive
% 1.64/1.01  --prep_sem_filter_out                   false
% 1.64/1.01  --pred_elim                             true
% 1.64/1.01  --res_sim_input                         true
% 1.64/1.01  --eq_ax_congr_red                       true
% 1.64/1.01  --pure_diseq_elim                       true
% 1.64/1.01  --brand_transform                       false
% 1.64/1.01  --non_eq_to_eq                          false
% 1.64/1.01  --prep_def_merge                        true
% 1.64/1.01  --prep_def_merge_prop_impl              false
% 1.64/1.01  --prep_def_merge_mbd                    true
% 1.64/1.01  --prep_def_merge_tr_red                 false
% 1.64/1.01  --prep_def_merge_tr_cl                  false
% 1.64/1.01  --smt_preprocessing                     true
% 1.64/1.01  --smt_ac_axioms                         fast
% 1.64/1.01  --preprocessed_out                      false
% 1.64/1.01  --preprocessed_stats                    false
% 1.64/1.01  
% 1.64/1.01  ------ Abstraction refinement Options
% 1.64/1.01  
% 1.64/1.01  --abstr_ref                             []
% 1.64/1.01  --abstr_ref_prep                        false
% 1.64/1.01  --abstr_ref_until_sat                   false
% 1.64/1.01  --abstr_ref_sig_restrict                funpre
% 1.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/1.01  --abstr_ref_under                       []
% 1.64/1.01  
% 1.64/1.01  ------ SAT Options
% 1.64/1.01  
% 1.64/1.01  --sat_mode                              false
% 1.64/1.01  --sat_fm_restart_options                ""
% 1.64/1.01  --sat_gr_def                            false
% 1.64/1.01  --sat_epr_types                         true
% 1.64/1.01  --sat_non_cyclic_types                  false
% 1.64/1.01  --sat_finite_models                     false
% 1.64/1.01  --sat_fm_lemmas                         false
% 1.64/1.01  --sat_fm_prep                           false
% 1.64/1.01  --sat_fm_uc_incr                        true
% 1.64/1.01  --sat_out_model                         small
% 1.64/1.01  --sat_out_clauses                       false
% 1.64/1.01  
% 1.64/1.01  ------ QBF Options
% 1.64/1.01  
% 1.64/1.01  --qbf_mode                              false
% 1.64/1.01  --qbf_elim_univ                         false
% 1.64/1.01  --qbf_dom_inst                          none
% 1.64/1.01  --qbf_dom_pre_inst                      false
% 1.64/1.01  --qbf_sk_in                             false
% 1.64/1.01  --qbf_pred_elim                         true
% 1.64/1.01  --qbf_split                             512
% 1.64/1.01  
% 1.64/1.01  ------ BMC1 Options
% 1.64/1.01  
% 1.64/1.01  --bmc1_incremental                      false
% 1.64/1.01  --bmc1_axioms                           reachable_all
% 1.64/1.01  --bmc1_min_bound                        0
% 1.64/1.01  --bmc1_max_bound                        -1
% 1.64/1.01  --bmc1_max_bound_default                -1
% 1.64/1.01  --bmc1_symbol_reachability              true
% 1.64/1.01  --bmc1_property_lemmas                  false
% 1.64/1.01  --bmc1_k_induction                      false
% 1.64/1.01  --bmc1_non_equiv_states                 false
% 1.64/1.01  --bmc1_deadlock                         false
% 1.64/1.01  --bmc1_ucm                              false
% 1.64/1.01  --bmc1_add_unsat_core                   none
% 1.64/1.01  --bmc1_unsat_core_children              false
% 1.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/1.01  --bmc1_out_stat                         full
% 1.64/1.01  --bmc1_ground_init                      false
% 1.64/1.01  --bmc1_pre_inst_next_state              false
% 1.64/1.01  --bmc1_pre_inst_state                   false
% 1.64/1.01  --bmc1_pre_inst_reach_state             false
% 1.64/1.01  --bmc1_out_unsat_core                   false
% 1.64/1.01  --bmc1_aig_witness_out                  false
% 1.64/1.01  --bmc1_verbose                          false
% 1.64/1.01  --bmc1_dump_clauses_tptp                false
% 1.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.64/1.01  --bmc1_dump_file                        -
% 1.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.64/1.01  --bmc1_ucm_extend_mode                  1
% 1.64/1.01  --bmc1_ucm_init_mode                    2
% 1.64/1.01  --bmc1_ucm_cone_mode                    none
% 1.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.64/1.01  --bmc1_ucm_relax_model                  4
% 1.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/1.01  --bmc1_ucm_layered_model                none
% 1.64/1.01  --bmc1_ucm_max_lemma_size               10
% 1.64/1.01  
% 1.64/1.01  ------ AIG Options
% 1.64/1.01  
% 1.64/1.01  --aig_mode                              false
% 1.64/1.01  
% 1.64/1.01  ------ Instantiation Options
% 1.64/1.01  
% 1.64/1.01  --instantiation_flag                    true
% 1.64/1.01  --inst_sos_flag                         false
% 1.64/1.01  --inst_sos_phase                        true
% 1.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/1.01  --inst_lit_sel_side                     none
% 1.64/1.01  --inst_solver_per_active                1400
% 1.64/1.01  --inst_solver_calls_frac                1.
% 1.64/1.01  --inst_passive_queue_type               priority_queues
% 1.64/1.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.64/1.01  --inst_passive_queues_freq              [25;2]
% 1.64/1.01  --inst_dismatching                      true
% 1.64/1.01  --inst_eager_unprocessed_to_passive     true
% 1.64/1.01  --inst_prop_sim_given                   true
% 1.64/1.01  --inst_prop_sim_new                     false
% 1.64/1.01  --inst_subs_new                         false
% 1.64/1.01  --inst_eq_res_simp                      false
% 1.64/1.01  --inst_subs_given                       false
% 1.64/1.01  --inst_orphan_elimination               true
% 1.64/1.01  --inst_learning_loop_flag               true
% 1.64/1.01  --inst_learning_start                   3000
% 1.64/1.01  --inst_learning_factor                  2
% 1.64/1.01  --inst_start_prop_sim_after_learn       3
% 1.64/1.01  --inst_sel_renew                        solver
% 1.64/1.01  --inst_lit_activity_flag                true
% 1.64/1.01  --inst_restr_to_given                   false
% 1.64/1.01  --inst_activity_threshold               500
% 1.64/1.01  --inst_out_proof                        true
% 1.64/1.01  
% 1.64/1.01  ------ Resolution Options
% 1.64/1.01  
% 1.64/1.01  --resolution_flag                       false
% 1.64/1.01  --res_lit_sel                           adaptive
% 1.64/1.01  --res_lit_sel_side                      none
% 1.64/1.01  --res_ordering                          kbo
% 1.64/1.01  --res_to_prop_solver                    active
% 1.64/1.01  --res_prop_simpl_new                    false
% 1.64/1.01  --res_prop_simpl_given                  true
% 1.64/1.01  --res_passive_queue_type                priority_queues
% 1.64/1.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.64/1.01  --res_passive_queues_freq               [15;5]
% 1.64/1.01  --res_forward_subs                      full
% 1.64/1.01  --res_backward_subs                     full
% 1.64/1.01  --res_forward_subs_resolution           true
% 1.64/1.01  --res_backward_subs_resolution          true
% 1.64/1.01  --res_orphan_elimination                true
% 1.64/1.01  --res_time_limit                        2.
% 1.64/1.01  --res_out_proof                         true
% 1.64/1.01  
% 1.64/1.01  ------ Superposition Options
% 1.64/1.01  
% 1.64/1.01  --superposition_flag                    true
% 1.64/1.01  --sup_passive_queue_type                priority_queues
% 1.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.64/1.01  --demod_completeness_check              fast
% 1.64/1.01  --demod_use_ground                      true
% 1.64/1.01  --sup_to_prop_solver                    passive
% 1.64/1.01  --sup_prop_simpl_new                    true
% 1.64/1.01  --sup_prop_simpl_given                  true
% 1.64/1.01  --sup_fun_splitting                     false
% 1.64/1.01  --sup_smt_interval                      50000
% 1.64/1.01  
% 1.64/1.01  ------ Superposition Simplification Setup
% 1.64/1.01  
% 1.64/1.01  --sup_indices_passive                   []
% 1.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.01  --sup_full_bw                           [BwDemod]
% 1.64/1.01  --sup_immed_triv                        [TrivRules]
% 1.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.01  --sup_immed_bw_main                     []
% 1.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/1.01  
% 1.64/1.01  ------ Combination Options
% 1.64/1.01  
% 1.64/1.01  --comb_res_mult                         3
% 1.64/1.01  --comb_sup_mult                         2
% 1.64/1.01  --comb_inst_mult                        10
% 1.64/1.01  
% 1.64/1.01  ------ Debug Options
% 1.64/1.01  
% 1.64/1.01  --dbg_backtrace                         false
% 1.64/1.01  --dbg_dump_prop_clauses                 false
% 1.64/1.01  --dbg_dump_prop_clauses_file            -
% 1.64/1.01  --dbg_out_stat                          false
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  ------ Proving...
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 1.64/1.01  
% 1.64/1.01  % SZS output start Saturation for theBenchmark.p
% 1.64/1.01  
% 1.64/1.01  fof(f8,axiom,(
% 1.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f26,plain,(
% 1.64/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.01    inference(ennf_transformation,[],[f8])).
% 1.64/1.01  
% 1.64/1.01  fof(f46,plain,(
% 1.64/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.01    inference(cnf_transformation,[],[f26])).
% 1.64/1.01  
% 1.64/1.01  fof(f14,conjecture,(
% 1.64/1.01    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f15,negated_conjecture,(
% 1.64/1.01    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 1.64/1.01    inference(negated_conjecture,[],[f14])).
% 1.64/1.01  
% 1.64/1.01  fof(f16,plain,(
% 1.64/1.01    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 1.64/1.01    inference(pure_predicate_removal,[],[f15])).
% 1.64/1.01  
% 1.64/1.01  fof(f33,plain,(
% 1.64/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.64/1.01    inference(ennf_transformation,[],[f16])).
% 1.64/1.01  
% 1.64/1.01  fof(f34,plain,(
% 1.64/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 1.64/1.01    inference(flattening,[],[f33])).
% 1.64/1.01  
% 1.64/1.01  fof(f38,plain,(
% 1.64/1.01    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.64/1.01    introduced(choice_axiom,[])).
% 1.64/1.01  
% 1.64/1.01  fof(f37,plain,(
% 1.64/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1))) )),
% 1.64/1.01    introduced(choice_axiom,[])).
% 1.64/1.01  
% 1.64/1.01  fof(f36,plain,(
% 1.64/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.64/1.01    introduced(choice_axiom,[])).
% 1.64/1.01  
% 1.64/1.01  fof(f39,plain,(
% 1.64/1.01    (((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.64/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37,f36])).
% 1.64/1.01  
% 1.64/1.01  fof(f62,plain,(
% 1.64/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f61,plain,(
% 1.64/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f10,axiom,(
% 1.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f28,plain,(
% 1.64/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.01    inference(ennf_transformation,[],[f10])).
% 1.64/1.01  
% 1.64/1.01  fof(f29,plain,(
% 1.64/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.01    inference(flattening,[],[f28])).
% 1.64/1.01  
% 1.64/1.01  fof(f35,plain,(
% 1.64/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.01    inference(nnf_transformation,[],[f29])).
% 1.64/1.01  
% 1.64/1.01  fof(f48,plain,(
% 1.64/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.01    inference(cnf_transformation,[],[f35])).
% 1.64/1.01  
% 1.64/1.01  fof(f1,axiom,(
% 1.64/1.01    v1_xboole_0(k1_xboole_0)),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f40,plain,(
% 1.64/1.01    v1_xboole_0(k1_xboole_0)),
% 1.64/1.01    inference(cnf_transformation,[],[f1])).
% 1.64/1.01  
% 1.64/1.01  fof(f12,axiom,(
% 1.64/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f30,plain,(
% 1.64/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.64/1.01    inference(ennf_transformation,[],[f12])).
% 1.64/1.01  
% 1.64/1.01  fof(f31,plain,(
% 1.64/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.64/1.01    inference(flattening,[],[f30])).
% 1.64/1.01  
% 1.64/1.01  fof(f54,plain,(
% 1.64/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.64/1.01    inference(cnf_transformation,[],[f31])).
% 1.64/1.01  
% 1.64/1.01  fof(f13,axiom,(
% 1.64/1.01    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f32,plain,(
% 1.64/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.64/1.01    inference(ennf_transformation,[],[f13])).
% 1.64/1.01  
% 1.64/1.01  fof(f55,plain,(
% 1.64/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.64/1.01    inference(cnf_transformation,[],[f32])).
% 1.64/1.01  
% 1.64/1.01  fof(f59,plain,(
% 1.64/1.01    l1_orders_2(sK1)),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f58,plain,(
% 1.64/1.01    ~v2_struct_0(sK1)),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f7,axiom,(
% 1.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f17,plain,(
% 1.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.64/1.01    inference(pure_predicate_removal,[],[f7])).
% 1.64/1.01  
% 1.64/1.01  fof(f25,plain,(
% 1.64/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.01    inference(ennf_transformation,[],[f17])).
% 1.64/1.01  
% 1.64/1.01  fof(f45,plain,(
% 1.64/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.01    inference(cnf_transformation,[],[f25])).
% 1.64/1.01  
% 1.64/1.01  fof(f4,axiom,(
% 1.64/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f22,plain,(
% 1.64/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.64/1.01    inference(ennf_transformation,[],[f4])).
% 1.64/1.01  
% 1.64/1.01  fof(f23,plain,(
% 1.64/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/1.01    inference(flattening,[],[f22])).
% 1.64/1.01  
% 1.64/1.01  fof(f43,plain,(
% 1.64/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.64/1.01    inference(cnf_transformation,[],[f23])).
% 1.64/1.01  
% 1.64/1.01  fof(f6,axiom,(
% 1.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f24,plain,(
% 1.64/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.01    inference(ennf_transformation,[],[f6])).
% 1.64/1.01  
% 1.64/1.01  fof(f44,plain,(
% 1.64/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.01    inference(cnf_transformation,[],[f24])).
% 1.64/1.01  
% 1.64/1.01  fof(f2,axiom,(
% 1.64/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f20,plain,(
% 1.64/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/1.01    inference(ennf_transformation,[],[f2])).
% 1.64/1.01  
% 1.64/1.01  fof(f41,plain,(
% 1.64/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.64/1.01    inference(cnf_transformation,[],[f20])).
% 1.64/1.01  
% 1.64/1.01  fof(f9,axiom,(
% 1.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f27,plain,(
% 1.64/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/1.01    inference(ennf_transformation,[],[f9])).
% 1.64/1.01  
% 1.64/1.01  fof(f47,plain,(
% 1.64/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.01    inference(cnf_transformation,[],[f27])).
% 1.64/1.01  
% 1.64/1.01  fof(f63,plain,(
% 1.64/1.01    k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f60,plain,(
% 1.64/1.01    v1_funct_1(sK2)),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f57,plain,(
% 1.64/1.01    l1_orders_2(sK0)),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f56,plain,(
% 1.64/1.01    ~v2_struct_0(sK0)),
% 1.64/1.01    inference(cnf_transformation,[],[f39])).
% 1.64/1.01  
% 1.64/1.01  fof(f50,plain,(
% 1.64/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/1.01    inference(cnf_transformation,[],[f35])).
% 1.64/1.01  
% 1.64/1.01  fof(f3,axiom,(
% 1.64/1.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/1.01  
% 1.64/1.01  fof(f21,plain,(
% 1.64/1.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.64/1.01    inference(ennf_transformation,[],[f3])).
% 1.64/1.01  
% 1.64/1.01  fof(f42,plain,(
% 1.64/1.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/1.01    inference(cnf_transformation,[],[f21])).
% 1.64/1.01  
% 1.64/1.01  cnf(c_244,plain,
% 1.64/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 1.64/1.01      theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_242,plain,
% 1.64/1.01      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.64/1.01      theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_241,plain,
% 1.64/1.01      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.64/1.01      theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_239,plain,
% 1.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.64/1.01      | v1_funct_2(X3,X4,X5)
% 1.64/1.01      | X3 != X0
% 1.64/1.01      | X4 != X1
% 1.64/1.01      | X5 != X2 ),
% 1.64/1.01      theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_237,plain,
% 1.64/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.64/1.01      theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_232,plain,
% 1.64/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.64/1.01      theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_229,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_6,plain,
% 1.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_17,negated_conjecture,
% 1.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.64/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_443,plain,
% 1.64/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | sK2 != X2 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_444,plain,
% 1.64/1.01      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_443]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_699,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k1_relset_1(X0_52,X1_52,sK2) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_444]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_844,plain,
% 1.64/1.01      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(equality_resolution,[status(thm)],[c_699]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_18,negated_conjecture,
% 1.64/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.64/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_13,plain,
% 1.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.01      | k1_relset_1(X1,X2,X0) = X1
% 1.64/1.01      | k1_xboole_0 = X2 ),
% 1.64/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_398,plain,
% 1.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.64/1.01      | k1_relset_1(X1,X2,X0) = X1
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.64/1.01      | sK2 != X0
% 1.64/1.01      | k1_xboole_0 = X2 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_399,plain,
% 1.64/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 1.64/1.01      | k1_relset_1(X0,X1,sK2) = X0
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | k1_xboole_0 = X1 ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_398]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_650,plain,
% 1.64/1.01      ( k1_relset_1(X0,X1,sK2) = X0
% 1.64/1.01      | u1_struct_0(sK1) != X1
% 1.64/1.01      | u1_struct_0(sK0) != X0
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | sK2 != sK2
% 1.64/1.01      | k1_xboole_0 = X1 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_399]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_651,plain,
% 1.64/1.01      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 1.64/1.01      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_650]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_694,plain,
% 1.64/1.01      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 1.64/1.01      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_651]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_953,plain,
% 1.64/1.01      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_844,c_694]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_0,plain,
% 1.64/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_14,plain,
% 1.64/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.64/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_269,plain,
% 1.64/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_15,plain,
% 1.64/1.01      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_20,negated_conjecture,
% 1.64/1.01      ( l1_orders_2(sK1) ),
% 1.64/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_287,plain,
% 1.64/1.01      ( l1_struct_0(X0) | sK1 != X0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_288,plain,
% 1.64/1.01      ( l1_struct_0(sK1) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_287]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_371,plain,
% 1.64/1.01      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_269,c_288]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_372,plain,
% 1.64/1.01      ( v2_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_371]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_21,negated_conjecture,
% 1.64/1.01      ( ~ v2_struct_0(sK1) ),
% 1.64/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_374,plain,
% 1.64/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 1.64/1.01      inference(global_propositional_subsumption,[status(thm)],[c_372,c_21]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_703,plain,
% 1.64/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_374]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_993,plain,
% 1.64/1.01      ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(global_propositional_subsumption,[status(thm)],[c_953,c_703]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_5,plain,
% 1.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 1.64/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_3,plain,
% 1.64/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.64/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_305,plain,
% 1.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.01      | ~ v1_relat_1(X0)
% 1.64/1.01      | k7_relat_1(X0,X1) = X0 ),
% 1.64/1.01      inference(resolution,[status(thm)],[c_5,c_3]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_4,plain,
% 1.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_309,plain,
% 1.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.01      | k7_relat_1(X0,X1) = X0 ),
% 1.64/1.01      inference(global_propositional_subsumption,
% 1.64/1.01                [status(thm)],
% 1.64/1.01                [c_305,c_5,c_4,c_3]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_389,plain,
% 1.64/1.01      ( k7_relat_1(X0,X1) = X0
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.64/1.01      | sK2 != X0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_309,c_17]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_390,plain,
% 1.64/1.01      ( k7_relat_1(sK2,X0) = sK2
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_389]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_701,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k7_relat_1(sK2,X0_52) = sK2 ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_390]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_841,plain,
% 1.64/1.01      ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
% 1.64/1.01      inference(equality_resolution,[status(thm)],[c_701]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_999,plain,
% 1.64/1.01      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_841]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1,plain,
% 1.64/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.64/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_452,plain,
% 1.64/1.01      ( v1_relat_1(X0)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.64/1.01      | sK2 != X0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_453,plain,
% 1.64/1.01      ( v1_relat_1(sK2)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_452]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_595,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
% 1.64/1.01      | sK2 != X2 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_453]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_596,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_595]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_697,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k2_relat_1(k7_relat_1(sK2,X2_52)) = k9_relat_1(sK2,X2_52) ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_596]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_704,plain,
% 1.64/1.01      ( k2_relat_1(k7_relat_1(sK2,X0_52)) = k9_relat_1(sK2,X0_52)
% 1.64/1.01      | ~ sP0_iProver_split ),
% 1.64/1.01      inference(splitting,
% 1.64/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.64/1.01                [c_697]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_778,plain,
% 1.64/1.01      ( k2_relat_1(k7_relat_1(sK2,X0_52)) = k9_relat_1(sK2,X0_52)
% 1.64/1.01      | sP0_iProver_split != iProver_top ),
% 1.64/1.01      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_706,plain,
% 1.64/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 1.64/1.01      inference(splitting,
% 1.64/1.01                [splitting(split),new_symbols(definition,[])],
% 1.64/1.01                [c_697]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_709,plain,( X0_55 = X0_55 ),theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_845,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.64/1.01      inference(instantiation,[status(thm)],[c_709]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_705,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | ~ sP1_iProver_split ),
% 1.64/1.01      inference(splitting,
% 1.64/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.64/1.01                [c_697]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_846,plain,
% 1.64/1.01      ( ~ sP1_iProver_split
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.64/1.01      inference(instantiation,[status(thm)],[c_705]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1318,plain,
% 1.64/1.01      ( k2_relat_1(k7_relat_1(sK2,X0_52)) = k9_relat_1(sK2,X0_52) ),
% 1.64/1.01      inference(global_propositional_subsumption,
% 1.64/1.01                [status(thm)],
% 1.64/1.01                [c_778,c_706,c_704,c_845,c_846]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1322,plain,
% 1.64/1.01      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 1.64/1.01      inference(superposition,[status(thm)],[c_999,c_1318]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_776,plain,
% 1.64/1.01      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.64/1.01      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_742,plain,
% 1.64/1.01      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.64/1.01      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_848,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.64/1.01      | sP1_iProver_split != iProver_top ),
% 1.64/1.01      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1312,plain,
% 1.64/1.01      ( sP0_iProver_split = iProver_top ),
% 1.64/1.01      inference(global_propositional_subsumption,
% 1.64/1.01                [status(thm)],
% 1.64/1.01                [c_776,c_742,c_845,c_848]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_777,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | sP1_iProver_split != iProver_top ),
% 1.64/1.01      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1267,plain,
% 1.64/1.01      ( sP1_iProver_split != iProver_top ),
% 1.64/1.01      inference(global_propositional_subsumption,
% 1.64/1.01                [status(thm)],
% 1.64/1.01                [c_777,c_845,c_848]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1004,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k7_relat_1(sK2,X0_52) = sK2 ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_701]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1003,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k1_relset_1(X0_52,X1_52,sK2) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_699]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_7,plain,
% 1.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_434,plain,
% 1.64/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | sK2 != X2 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_435,plain,
% 1.64/1.01      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_434]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_700,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k2_relset_1(X0_52,X1_52,sK2) = k2_relat_1(sK2) ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_435]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1002,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k2_relset_1(X0_52,X1_52,sK2) = k2_relat_1(sK2) ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_700]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_16,negated_conjecture,
% 1.64/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.64/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.64/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_19,negated_conjecture,
% 1.64/1.01      ( v1_funct_1(sK2) ),
% 1.64/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_325,plain,
% 1.64/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.64/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_529,plain,
% 1.64/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_325,c_17]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_618,plain,
% 1.64/1.01      ( k2_funct_1(sK2) != sK2
% 1.64/1.01      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_529,c_18]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_696,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_618]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1001,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | u1_struct_0(sK1) != k1_relat_1(sK2)
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_696]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_22,negated_conjecture,
% 1.64/1.01      ( l1_orders_2(sK0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_294,plain,
% 1.64/1.01      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_295,plain,
% 1.64/1.01      ( l1_struct_0(sK0) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_294]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_379,plain,
% 1.64/1.01      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK0 != X0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_269,c_295]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_380,plain,
% 1.64/1.01      ( v2_struct_0(sK0) | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_379]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_23,negated_conjecture,
% 1.64/1.01      ( ~ v2_struct_0(sK0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_382,plain,
% 1.64/1.01      ( u1_struct_0(sK0) != k1_xboole_0 ),
% 1.64/1.01      inference(global_propositional_subsumption,[status(thm)],[c_380,c_23]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_702,plain,
% 1.64/1.01      ( u1_struct_0(sK0) != k1_xboole_0 ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_382]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_1000,plain,
% 1.64/1.01      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_702]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_11,plain,
% 1.64/1.01      ( v1_funct_2(X0,X1,X2)
% 1.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/1.01      | k1_relset_1(X1,X2,X0) != X1
% 1.64/1.01      | k1_xboole_0 = X2 ),
% 1.64/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_416,plain,
% 1.64/1.01      ( v1_funct_2(X0,X1,X2)
% 1.64/1.01      | k1_relset_1(X1,X2,X0) != X1
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.64/1.01      | sK2 != X0
% 1.64/1.01      | k1_xboole_0 = X2 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_417,plain,
% 1.64/1.01      ( v1_funct_2(sK2,X0,X1)
% 1.64/1.01      | k1_relset_1(X0,X1,sK2) != X0
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | k1_xboole_0 = X1 ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_416]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_631,plain,
% 1.64/1.01      ( k1_relset_1(X0,X1,sK2) != X0
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | u1_struct_0(sK1) != X0
% 1.64/1.01      | u1_struct_0(sK0) != X1
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.64/1.01      | k1_xboole_0 = X1 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_529,c_417]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_632,plain,
% 1.64/1.01      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.64/1.01      | k1_xboole_0 = u1_struct_0(sK0) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_631]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_695,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.64/1.01      | k1_xboole_0 = u1_struct_0(sK0) ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_632]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_711,plain,
% 1.64/1.01      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 1.64/1.01      theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_865,plain,
% 1.64/1.01      ( u1_struct_0(sK0) != X0_52
% 1.64/1.01      | u1_struct_0(sK0) = k1_xboole_0
% 1.64/1.01      | k1_xboole_0 != X0_52 ),
% 1.64/1.01      inference(instantiation,[status(thm)],[c_711]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_878,plain,
% 1.64/1.01      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.64/1.01      | u1_struct_0(sK0) = k1_xboole_0
% 1.64/1.01      | k1_xboole_0 != u1_struct_0(sK0) ),
% 1.64/1.01      inference(instantiation,[status(thm)],[c_865]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_707,plain,( X0_52 = X0_52 ),theory(equality) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_879,plain,
% 1.64/1.01      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.64/1.01      inference(instantiation,[status(thm)],[c_707]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_908,plain,
% 1.64/1.01      ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.64/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 1.64/1.01      inference(global_propositional_subsumption,
% 1.64/1.01                [status(thm)],
% 1.64/1.01                [c_695,c_702,c_878,c_879]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_909,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.64/1.01      inference(renaming,[status(thm)],[c_908]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_998,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
% 1.64/1.01      | k2_funct_1(sK2) != sK2
% 1.64/1.01      | k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),sK2) != u1_struct_0(sK1)
% 1.64/1.01      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_909]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_997,plain,
% 1.64/1.01      ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_844]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_860,plain,
% 1.64/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.64/1.01      inference(equality_resolution,[status(thm)],[c_700]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_996,plain,
% 1.64/1.01      ( k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.64/1.01      inference(demodulation,[status(thm)],[c_993,c_860]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_2,plain,
% 1.64/1.01      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 1.64/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_586,plain,
% 1.64/1.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.64/1.01      | sK2 != X0 ),
% 1.64/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_453]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_587,plain,
% 1.64/1.01      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 1.64/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.64/1.01      inference(unflattening,[status(thm)],[c_586]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_698,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))
% 1.64/1.01      | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(subtyping,[status(esa)],[c_587]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_847,plain,
% 1.64/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.64/1.01      | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(instantiation,[status(thm)],[c_698]) ).
% 1.64/1.01  
% 1.64/1.01  cnf(c_914,plain,
% 1.64/1.01      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.64/1.01      inference(global_propositional_subsumption,
% 1.64/1.01                [status(thm)],
% 1.64/1.01                [c_698,c_845,c_847]) ).
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  % SZS output end Saturation for theBenchmark.p
% 1.64/1.01  
% 1.64/1.01  ------                               Statistics
% 1.64/1.01  
% 1.64/1.01  ------ General
% 1.64/1.01  
% 1.64/1.01  abstr_ref_over_cycles:                  0
% 1.64/1.01  abstr_ref_under_cycles:                 0
% 1.64/1.01  gc_basic_clause_elim:                   0
% 1.64/1.01  forced_gc_time:                         0
% 1.64/1.01  parsing_time:                           0.011
% 1.64/1.01  unif_index_cands_time:                  0.
% 1.64/1.01  unif_index_add_time:                    0.
% 1.64/1.01  orderings_time:                         0.
% 1.64/1.01  out_proof_time:                         0.
% 1.64/1.01  total_time:                             0.119
% 1.64/1.01  num_of_symbols:                         59
% 1.64/1.01  num_of_terms:                           1297
% 1.64/1.01  
% 1.64/1.01  ------ Preprocessing
% 1.64/1.01  
% 1.64/1.01  num_of_splits:                          2
% 1.64/1.01  num_of_split_atoms:                     2
% 1.64/1.01  num_of_reused_defs:                     0
% 1.64/1.01  num_eq_ax_congr_red:                    24
% 1.64/1.01  num_of_sem_filtered_clauses:            0
% 1.64/1.01  num_of_subtypes:                        5
% 1.64/1.01  monotx_restored_types:                  0
% 1.64/1.01  sat_num_of_epr_types:                   0
% 1.64/1.01  sat_num_of_non_cyclic_types:            0
% 1.64/1.01  sat_guarded_non_collapsed_types:        0
% 1.64/1.01  num_pure_diseq_elim:                    0
% 1.64/1.01  simp_replaced_by:                       0
% 1.64/1.01  res_preprocessed:                       63
% 1.64/1.01  prep_upred:                             0
% 1.64/1.01  prep_unflattend:                        36
% 1.64/1.01  smt_new_axioms:                         0
% 1.64/1.01  pred_elim_cands:                        0
% 1.64/1.01  pred_elim:                              9
% 1.64/1.01  pred_elim_cl:                           14
% 1.64/1.01  pred_elim_cycles:                       11
% 1.64/1.01  merged_defs:                            0
% 1.64/1.01  merged_defs_ncl:                        0
% 1.64/1.01  bin_hyper_res:                          0
% 1.64/1.01  prep_cycles:                            3
% 1.64/1.01  pred_elim_time:                         0.013
% 1.64/1.01  splitting_time:                         0.
% 1.64/1.01  sem_filter_time:                        0.
% 1.64/1.01  monotx_time:                            0.
% 1.64/1.01  subtype_inf_time:                       0.
% 1.64/1.01  
% 1.64/1.01  ------ Problem properties
% 1.64/1.01  
% 1.64/1.01  clauses:                                12
% 1.64/1.01  conjectures:                            0
% 1.64/1.01  epr:                                    1
% 1.64/1.01  horn:                                   10
% 1.64/1.01  ground:                                 6
% 1.64/1.01  unary:                                  2
% 1.64/1.01  binary:                                 8
% 1.64/1.01  lits:                                   27
% 1.64/1.01  lits_eq:                                23
% 1.64/1.01  fd_pure:                                0
% 1.64/1.01  fd_pseudo:                              0
% 1.64/1.01  fd_cond:                                0
% 1.64/1.01  fd_pseudo_cond:                         0
% 1.64/1.01  ac_symbols:                             0
% 1.64/1.01  
% 1.64/1.01  ------ Propositional Solver
% 1.64/1.01  
% 1.64/1.01  prop_solver_calls:                      25
% 1.64/1.01  prop_fast_solver_calls:                 413
% 1.64/1.01  smt_solver_calls:                       0
% 1.64/1.01  smt_fast_solver_calls:                  0
% 1.64/1.01  prop_num_of_clauses:                    384
% 1.64/1.01  prop_preprocess_simplified:             1721
% 1.64/1.01  prop_fo_subsumed:                       9
% 1.64/1.01  prop_solver_time:                       0.
% 1.64/1.01  smt_solver_time:                        0.
% 1.64/1.01  smt_fast_solver_time:                   0.
% 1.64/1.01  prop_fast_solver_time:                  0.
% 1.64/1.01  prop_unsat_core_time:                   0.
% 1.64/1.01  
% 1.64/1.01  ------ QBF
% 1.64/1.01  
% 1.64/1.01  qbf_q_res:                              0
% 1.64/1.01  qbf_num_tautologies:                    0
% 1.64/1.01  qbf_prep_cycles:                        0
% 1.64/1.01  
% 1.64/1.01  ------ BMC1
% 1.64/1.01  
% 1.64/1.01  bmc1_current_bound:                     -1
% 1.64/1.01  bmc1_last_solved_bound:                 -1
% 1.64/1.01  bmc1_unsat_core_size:                   -1
% 1.64/1.01  bmc1_unsat_core_parents_size:           -1
% 1.64/1.01  bmc1_merge_next_fun:                    0
% 1.64/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.64/1.01  
% 1.64/1.01  ------ Instantiation
% 1.64/1.01  
% 1.64/1.01  inst_num_of_clauses:                    155
% 1.64/1.01  inst_num_in_passive:                    13
% 1.64/1.01  inst_num_in_active:                     130
% 1.64/1.01  inst_num_in_unprocessed:                12
% 1.64/1.01  inst_num_of_loops:                      140
% 1.64/1.01  inst_num_of_learning_restarts:          0
% 1.64/1.01  inst_num_moves_active_passive:          3
% 1.64/1.01  inst_lit_activity:                      0
% 1.64/1.01  inst_lit_activity_moves:                0
% 1.64/1.01  inst_num_tautologies:                   0
% 1.64/1.01  inst_num_prop_implied:                  0
% 1.64/1.01  inst_num_existing_simplified:           0
% 1.64/1.01  inst_num_eq_res_simplified:             0
% 1.64/1.01  inst_num_child_elim:                    0
% 1.64/1.01  inst_num_of_dismatching_blockings:      27
% 1.64/1.01  inst_num_of_non_proper_insts:           174
% 1.64/1.01  inst_num_of_duplicates:                 0
% 1.64/1.01  inst_inst_num_from_inst_to_res:         0
% 1.64/1.01  inst_dismatching_checking_time:         0.
% 1.64/1.01  
% 1.64/1.01  ------ Resolution
% 1.64/1.01  
% 1.64/1.01  res_num_of_clauses:                     0
% 1.64/1.01  res_num_in_passive:                     0
% 1.64/1.01  res_num_in_active:                      0
% 1.64/1.01  res_num_of_loops:                       66
% 1.64/1.01  res_forward_subset_subsumed:            49
% 1.64/1.01  res_backward_subset_subsumed:           0
% 1.64/1.01  res_forward_subsumed:                   0
% 1.64/1.01  res_backward_subsumed:                  0
% 1.64/1.01  res_forward_subsumption_resolution:     0
% 1.64/1.01  res_backward_subsumption_resolution:    0
% 1.64/1.01  res_clause_to_clause_subsumption:       31
% 1.64/1.01  res_orphan_elimination:                 0
% 1.64/1.01  res_tautology_del:                      51
% 1.64/1.01  res_num_eq_res_simplified:              0
% 1.64/1.01  res_num_sel_changes:                    0
% 1.64/1.01  res_moves_from_active_to_pass:          0
% 1.64/1.01  
% 1.64/1.01  ------ Superposition
% 1.64/1.01  
% 1.64/1.01  sup_time_total:                         0.
% 1.64/1.01  sup_time_generating:                    0.
% 1.64/1.01  sup_time_sim_full:                      0.
% 1.64/1.01  sup_time_sim_immed:                     0.
% 1.64/1.01  
% 1.64/1.01  sup_num_of_clauses:                     16
% 1.64/1.01  sup_num_in_active:                      16
% 1.64/1.01  sup_num_in_passive:                     0
% 1.64/1.01  sup_num_of_loops:                       26
% 1.64/1.01  sup_fw_superposition:                   1
% 1.64/1.01  sup_bw_superposition:                   0
% 1.64/1.01  sup_immediate_simplified:               0
% 1.64/1.01  sup_given_eliminated:                   0
% 1.64/1.01  comparisons_done:                       0
% 1.64/1.01  comparisons_avoided:                    0
% 1.64/1.01  
% 1.64/1.01  ------ Simplifications
% 1.64/1.01  
% 1.64/1.01  
% 1.64/1.01  sim_fw_subset_subsumed:                 0
% 1.64/1.01  sim_bw_subset_subsumed:                 0
% 1.64/1.01  sim_fw_subsumed:                        0
% 1.64/1.01  sim_bw_subsumed:                        0
% 1.64/1.01  sim_fw_subsumption_res:                 0
% 1.64/1.01  sim_bw_subsumption_res:                 0
% 1.64/1.01  sim_tautology_del:                      0
% 1.64/1.01  sim_eq_tautology_del:                   0
% 1.64/1.01  sim_eq_res_simp:                        0
% 1.64/1.01  sim_fw_demodulated:                     0
% 1.64/1.01  sim_bw_demodulated:                     10
% 1.64/1.01  sim_light_normalised:                   0
% 1.64/1.01  sim_joinable_taut:                      0
% 1.64/1.01  sim_joinable_simp:                      0
% 1.64/1.01  sim_ac_normalised:                      0
% 1.64/1.01  sim_smt_subsumption:                    0
% 1.64/1.01  
%------------------------------------------------------------------------------
