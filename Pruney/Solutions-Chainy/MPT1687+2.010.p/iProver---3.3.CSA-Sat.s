%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:14 EST 2020

% Result     : CounterSatisfiable 2.00s
% Output     : Saturation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 948 expanded)
%              Number of clauses        :   93 ( 263 expanded)
%              Number of leaves         :   31 ( 262 expanded)
%              Depth                    :   14
%              Number of atoms          :  627 (7165 expanded)
%              Number of equality atoms :  209 (1155 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f52,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f45,f44,f43])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_353,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_352,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_350,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_349,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_347,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_340,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_339,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_338,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_336,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1347,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_197,plain,
    ( ~ v2_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_7,c_2])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_197])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1489,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1491,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1748,plain,
    ( k1_relset_1(X0,X0,k6_partfun1(X0)) = k1_relat_1(k6_partfun1(X0)) ),
    inference(superposition,[status(thm)],[c_1489,c_1491])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_491,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_18])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_18,c_8,c_7])).

cnf(c_496,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_20,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 != X1
    | k1_relat_1(X0) = X1
    | k6_partfun1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_496,c_20])).

cnf(c_538,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_1487,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_1683,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1489,c_1487])).

cnf(c_2182,plain,
    ( k1_relset_1(X0,X0,k6_partfun1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1748,c_1683])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1488,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1749,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1488,c_1491])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_957,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_958,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_960,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_27])).

cnf(c_1882,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1749,c_960])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_379,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_25,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_397,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_398,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_435,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_379,c_398])).

cnf(c_436,plain,
    ( v2_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1934,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_31,c_436])).

cnf(c_1942,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1934,c_1488])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_404,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_405,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_443,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_379,c_405])).

cnf(c_444,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_446,plain,
    ( u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_33])).

cnf(c_1941,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1934,c_446])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_415,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_968,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_415,c_28])).

cnf(c_1485,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_1940,plain,
    ( u1_struct_0(sK1) != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != sK2
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1934,c_1485])).

cnf(c_14,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_938,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_relset_1(X1,X2,X0) != X1
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != X2
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != X0
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_415])).

cnf(c_939,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_1486,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_940,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_1349,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1556,plain,
    ( u1_struct_0(sK0) != X0
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_1612,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_1348,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1613,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_1630,plain,
    ( k2_funct_1(sK2) != sK2
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1486,c_33,c_444,c_940,c_1612,c_1613])).

cnf(c_1631,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1630])).

cnf(c_1939,plain,
    ( k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != sK2
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1934,c_1631])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1490,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1739,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1488,c_1490])).

cnf(c_1938,plain,
    ( k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1934,c_1739])).

cnf(c_1937,plain,
    ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1934,c_1749])).

cnf(c_1738,plain,
    ( k2_relset_1(X0,X0,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0)) ),
    inference(superposition,[status(thm)],[c_1489,c_1490])).

cnf(c_438,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.00/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/0.99  
% 2.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.00/0.99  
% 2.00/0.99  ------  iProver source info
% 2.00/0.99  
% 2.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.00/0.99  git: non_committed_changes: false
% 2.00/0.99  git: last_make_outside_of_git: false
% 2.00/0.99  
% 2.00/0.99  ------ 
% 2.00/0.99  
% 2.00/0.99  ------ Input Options
% 2.00/0.99  
% 2.00/0.99  --out_options                           all
% 2.00/0.99  --tptp_safe_out                         true
% 2.00/0.99  --problem_path                          ""
% 2.00/0.99  --include_path                          ""
% 2.00/0.99  --clausifier                            res/vclausify_rel
% 2.00/0.99  --clausifier_options                    --mode clausify
% 2.00/0.99  --stdin                                 false
% 2.00/0.99  --stats_out                             all
% 2.00/0.99  
% 2.00/0.99  ------ General Options
% 2.00/0.99  
% 2.00/0.99  --fof                                   false
% 2.00/0.99  --time_out_real                         305.
% 2.00/0.99  --time_out_virtual                      -1.
% 2.00/0.99  --symbol_type_check                     false
% 2.00/0.99  --clausify_out                          false
% 2.00/0.99  --sig_cnt_out                           false
% 2.00/0.99  --trig_cnt_out                          false
% 2.00/0.99  --trig_cnt_out_tolerance                1.
% 2.00/0.99  --trig_cnt_out_sk_spl                   false
% 2.00/0.99  --abstr_cl_out                          false
% 2.00/0.99  
% 2.00/0.99  ------ Global Options
% 2.00/0.99  
% 2.00/0.99  --schedule                              default
% 2.00/0.99  --add_important_lit                     false
% 2.00/0.99  --prop_solver_per_cl                    1000
% 2.00/0.99  --min_unsat_core                        false
% 2.00/0.99  --soft_assumptions                      false
% 2.00/0.99  --soft_lemma_size                       3
% 2.00/0.99  --prop_impl_unit_size                   0
% 2.00/0.99  --prop_impl_unit                        []
% 2.00/0.99  --share_sel_clauses                     true
% 2.00/0.99  --reset_solvers                         false
% 2.00/0.99  --bc_imp_inh                            [conj_cone]
% 2.00/0.99  --conj_cone_tolerance                   3.
% 2.00/0.99  --extra_neg_conj                        none
% 2.00/0.99  --large_theory_mode                     true
% 2.00/0.99  --prolific_symb_bound                   200
% 2.00/0.99  --lt_threshold                          2000
% 2.00/0.99  --clause_weak_htbl                      true
% 2.00/0.99  --gc_record_bc_elim                     false
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing Options
% 2.00/0.99  
% 2.00/0.99  --preprocessing_flag                    true
% 2.00/0.99  --time_out_prep_mult                    0.1
% 2.00/0.99  --splitting_mode                        input
% 2.00/0.99  --splitting_grd                         true
% 2.00/0.99  --splitting_cvd                         false
% 2.00/0.99  --splitting_cvd_svl                     false
% 2.00/0.99  --splitting_nvd                         32
% 2.00/0.99  --sub_typing                            true
% 2.00/0.99  --prep_gs_sim                           true
% 2.00/0.99  --prep_unflatten                        true
% 2.00/0.99  --prep_res_sim                          true
% 2.00/0.99  --prep_upred                            true
% 2.00/0.99  --prep_sem_filter                       exhaustive
% 2.00/0.99  --prep_sem_filter_out                   false
% 2.00/0.99  --pred_elim                             true
% 2.00/0.99  --res_sim_input                         true
% 2.00/0.99  --eq_ax_congr_red                       true
% 2.00/0.99  --pure_diseq_elim                       true
% 2.00/0.99  --brand_transform                       false
% 2.00/0.99  --non_eq_to_eq                          false
% 2.00/0.99  --prep_def_merge                        true
% 2.00/0.99  --prep_def_merge_prop_impl              false
% 2.00/0.99  --prep_def_merge_mbd                    true
% 2.00/0.99  --prep_def_merge_tr_red                 false
% 2.00/0.99  --prep_def_merge_tr_cl                  false
% 2.00/0.99  --smt_preprocessing                     true
% 2.00/0.99  --smt_ac_axioms                         fast
% 2.00/0.99  --preprocessed_out                      false
% 2.00/0.99  --preprocessed_stats                    false
% 2.00/0.99  
% 2.00/0.99  ------ Abstraction refinement Options
% 2.00/0.99  
% 2.00/0.99  --abstr_ref                             []
% 2.00/0.99  --abstr_ref_prep                        false
% 2.00/0.99  --abstr_ref_until_sat                   false
% 2.00/0.99  --abstr_ref_sig_restrict                funpre
% 2.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/0.99  --abstr_ref_under                       []
% 2.00/0.99  
% 2.00/0.99  ------ SAT Options
% 2.00/0.99  
% 2.00/0.99  --sat_mode                              false
% 2.00/0.99  --sat_fm_restart_options                ""
% 2.00/0.99  --sat_gr_def                            false
% 2.00/0.99  --sat_epr_types                         true
% 2.00/0.99  --sat_non_cyclic_types                  false
% 2.00/0.99  --sat_finite_models                     false
% 2.00/0.99  --sat_fm_lemmas                         false
% 2.00/0.99  --sat_fm_prep                           false
% 2.00/0.99  --sat_fm_uc_incr                        true
% 2.00/0.99  --sat_out_model                         small
% 2.00/0.99  --sat_out_clauses                       false
% 2.00/0.99  
% 2.00/0.99  ------ QBF Options
% 2.00/0.99  
% 2.00/0.99  --qbf_mode                              false
% 2.00/0.99  --qbf_elim_univ                         false
% 2.00/0.99  --qbf_dom_inst                          none
% 2.00/0.99  --qbf_dom_pre_inst                      false
% 2.00/0.99  --qbf_sk_in                             false
% 2.00/0.99  --qbf_pred_elim                         true
% 2.00/0.99  --qbf_split                             512
% 2.00/0.99  
% 2.00/0.99  ------ BMC1 Options
% 2.00/0.99  
% 2.00/0.99  --bmc1_incremental                      false
% 2.00/0.99  --bmc1_axioms                           reachable_all
% 2.00/0.99  --bmc1_min_bound                        0
% 2.00/0.99  --bmc1_max_bound                        -1
% 2.00/0.99  --bmc1_max_bound_default                -1
% 2.00/0.99  --bmc1_symbol_reachability              true
% 2.00/0.99  --bmc1_property_lemmas                  false
% 2.00/0.99  --bmc1_k_induction                      false
% 2.00/0.99  --bmc1_non_equiv_states                 false
% 2.00/0.99  --bmc1_deadlock                         false
% 2.00/0.99  --bmc1_ucm                              false
% 2.00/0.99  --bmc1_add_unsat_core                   none
% 2.00/0.99  --bmc1_unsat_core_children              false
% 2.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/0.99  --bmc1_out_stat                         full
% 2.00/0.99  --bmc1_ground_init                      false
% 2.00/0.99  --bmc1_pre_inst_next_state              false
% 2.00/0.99  --bmc1_pre_inst_state                   false
% 2.00/0.99  --bmc1_pre_inst_reach_state             false
% 2.00/0.99  --bmc1_out_unsat_core                   false
% 2.00/0.99  --bmc1_aig_witness_out                  false
% 2.00/0.99  --bmc1_verbose                          false
% 2.00/0.99  --bmc1_dump_clauses_tptp                false
% 2.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.00/0.99  --bmc1_dump_file                        -
% 2.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.00/0.99  --bmc1_ucm_extend_mode                  1
% 2.00/0.99  --bmc1_ucm_init_mode                    2
% 2.00/0.99  --bmc1_ucm_cone_mode                    none
% 2.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.00/0.99  --bmc1_ucm_relax_model                  4
% 2.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/0.99  --bmc1_ucm_layered_model                none
% 2.00/0.99  --bmc1_ucm_max_lemma_size               10
% 2.00/0.99  
% 2.00/0.99  ------ AIG Options
% 2.00/0.99  
% 2.00/0.99  --aig_mode                              false
% 2.00/0.99  
% 2.00/0.99  ------ Instantiation Options
% 2.00/0.99  
% 2.00/0.99  --instantiation_flag                    true
% 2.00/0.99  --inst_sos_flag                         false
% 2.00/0.99  --inst_sos_phase                        true
% 2.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel_side                     num_symb
% 2.00/0.99  --inst_solver_per_active                1400
% 2.00/0.99  --inst_solver_calls_frac                1.
% 2.00/0.99  --inst_passive_queue_type               priority_queues
% 2.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/0.99  --inst_passive_queues_freq              [25;2]
% 2.00/0.99  --inst_dismatching                      true
% 2.00/0.99  --inst_eager_unprocessed_to_passive     true
% 2.00/0.99  --inst_prop_sim_given                   true
% 2.00/0.99  --inst_prop_sim_new                     false
% 2.00/0.99  --inst_subs_new                         false
% 2.00/0.99  --inst_eq_res_simp                      false
% 2.00/0.99  --inst_subs_given                       false
% 2.00/0.99  --inst_orphan_elimination               true
% 2.00/0.99  --inst_learning_loop_flag               true
% 2.00/0.99  --inst_learning_start                   3000
% 2.00/0.99  --inst_learning_factor                  2
% 2.00/0.99  --inst_start_prop_sim_after_learn       3
% 2.00/0.99  --inst_sel_renew                        solver
% 2.00/0.99  --inst_lit_activity_flag                true
% 2.00/0.99  --inst_restr_to_given                   false
% 2.00/0.99  --inst_activity_threshold               500
% 2.00/0.99  --inst_out_proof                        true
% 2.00/0.99  
% 2.00/0.99  ------ Resolution Options
% 2.00/0.99  
% 2.00/0.99  --resolution_flag                       true
% 2.00/0.99  --res_lit_sel                           adaptive
% 2.00/0.99  --res_lit_sel_side                      none
% 2.00/0.99  --res_ordering                          kbo
% 2.00/0.99  --res_to_prop_solver                    active
% 2.00/0.99  --res_prop_simpl_new                    false
% 2.00/0.99  --res_prop_simpl_given                  true
% 2.00/0.99  --res_passive_queue_type                priority_queues
% 2.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/0.99  --res_passive_queues_freq               [15;5]
% 2.00/0.99  --res_forward_subs                      full
% 2.00/0.99  --res_backward_subs                     full
% 2.00/0.99  --res_forward_subs_resolution           true
% 2.00/0.99  --res_backward_subs_resolution          true
% 2.00/0.99  --res_orphan_elimination                true
% 2.00/0.99  --res_time_limit                        2.
% 2.00/0.99  --res_out_proof                         true
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Options
% 2.00/0.99  
% 2.00/0.99  --superposition_flag                    true
% 2.00/0.99  --sup_passive_queue_type                priority_queues
% 2.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.00/0.99  --demod_completeness_check              fast
% 2.00/0.99  --demod_use_ground                      true
% 2.00/0.99  --sup_to_prop_solver                    passive
% 2.00/0.99  --sup_prop_simpl_new                    true
% 2.00/0.99  --sup_prop_simpl_given                  true
% 2.00/0.99  --sup_fun_splitting                     false
% 2.00/0.99  --sup_smt_interval                      50000
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Simplification Setup
% 2.00/0.99  
% 2.00/0.99  --sup_indices_passive                   []
% 2.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_full_bw                           [BwDemod]
% 2.00/0.99  --sup_immed_triv                        [TrivRules]
% 2.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_immed_bw_main                     []
% 2.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  
% 2.00/0.99  ------ Combination Options
% 2.00/0.99  
% 2.00/0.99  --comb_res_mult                         3
% 2.00/0.99  --comb_sup_mult                         2
% 2.00/0.99  --comb_inst_mult                        10
% 2.00/0.99  
% 2.00/0.99  ------ Debug Options
% 2.00/0.99  
% 2.00/0.99  --dbg_backtrace                         false
% 2.00/0.99  --dbg_dump_prop_clauses                 false
% 2.00/0.99  --dbg_dump_prop_clauses_file            -
% 2.00/0.99  --dbg_out_stat                          false
% 2.00/0.99  ------ Parsing...
% 2.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.00/0.99  ------ Proving...
% 2.00/0.99  ------ Problem Properties 
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  clauses                                 10
% 2.00/0.99  conjectures                             1
% 2.00/0.99  EPR                                     0
% 2.00/0.99  Horn                                    9
% 2.00/0.99  unary                                   4
% 2.00/0.99  binary                                  4
% 2.00/0.99  lits                                    21
% 2.00/0.99  lits eq                                 14
% 2.00/0.99  fd_pure                                 0
% 2.00/0.99  fd_pseudo                               0
% 2.00/0.99  fd_cond                                 0
% 2.00/0.99  fd_pseudo_cond                          0
% 2.00/0.99  AC symbols                              0
% 2.00/0.99  
% 2.00/0.99  ------ Schedule dynamic 5 is on 
% 2.00/0.99  
% 2.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  ------ 
% 2.00/0.99  Current options:
% 2.00/0.99  ------ 
% 2.00/0.99  
% 2.00/0.99  ------ Input Options
% 2.00/0.99  
% 2.00/0.99  --out_options                           all
% 2.00/0.99  --tptp_safe_out                         true
% 2.00/0.99  --problem_path                          ""
% 2.00/0.99  --include_path                          ""
% 2.00/0.99  --clausifier                            res/vclausify_rel
% 2.00/0.99  --clausifier_options                    --mode clausify
% 2.00/0.99  --stdin                                 false
% 2.00/0.99  --stats_out                             all
% 2.00/0.99  
% 2.00/0.99  ------ General Options
% 2.00/0.99  
% 2.00/0.99  --fof                                   false
% 2.00/0.99  --time_out_real                         305.
% 2.00/0.99  --time_out_virtual                      -1.
% 2.00/0.99  --symbol_type_check                     false
% 2.00/0.99  --clausify_out                          false
% 2.00/0.99  --sig_cnt_out                           false
% 2.00/0.99  --trig_cnt_out                          false
% 2.00/0.99  --trig_cnt_out_tolerance                1.
% 2.00/0.99  --trig_cnt_out_sk_spl                   false
% 2.00/0.99  --abstr_cl_out                          false
% 2.00/0.99  
% 2.00/0.99  ------ Global Options
% 2.00/0.99  
% 2.00/0.99  --schedule                              default
% 2.00/0.99  --add_important_lit                     false
% 2.00/0.99  --prop_solver_per_cl                    1000
% 2.00/0.99  --min_unsat_core                        false
% 2.00/0.99  --soft_assumptions                      false
% 2.00/0.99  --soft_lemma_size                       3
% 2.00/0.99  --prop_impl_unit_size                   0
% 2.00/0.99  --prop_impl_unit                        []
% 2.00/0.99  --share_sel_clauses                     true
% 2.00/0.99  --reset_solvers                         false
% 2.00/0.99  --bc_imp_inh                            [conj_cone]
% 2.00/0.99  --conj_cone_tolerance                   3.
% 2.00/0.99  --extra_neg_conj                        none
% 2.00/0.99  --large_theory_mode                     true
% 2.00/0.99  --prolific_symb_bound                   200
% 2.00/0.99  --lt_threshold                          2000
% 2.00/0.99  --clause_weak_htbl                      true
% 2.00/0.99  --gc_record_bc_elim                     false
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing Options
% 2.00/0.99  
% 2.00/0.99  --preprocessing_flag                    true
% 2.00/0.99  --time_out_prep_mult                    0.1
% 2.00/0.99  --splitting_mode                        input
% 2.00/0.99  --splitting_grd                         true
% 2.00/0.99  --splitting_cvd                         false
% 2.00/0.99  --splitting_cvd_svl                     false
% 2.00/0.99  --splitting_nvd                         32
% 2.00/0.99  --sub_typing                            true
% 2.00/0.99  --prep_gs_sim                           true
% 2.00/0.99  --prep_unflatten                        true
% 2.00/0.99  --prep_res_sim                          true
% 2.00/0.99  --prep_upred                            true
% 2.00/0.99  --prep_sem_filter                       exhaustive
% 2.00/0.99  --prep_sem_filter_out                   false
% 2.00/0.99  --pred_elim                             true
% 2.00/0.99  --res_sim_input                         true
% 2.00/0.99  --eq_ax_congr_red                       true
% 2.00/0.99  --pure_diseq_elim                       true
% 2.00/0.99  --brand_transform                       false
% 2.00/0.99  --non_eq_to_eq                          false
% 2.00/0.99  --prep_def_merge                        true
% 2.00/0.99  --prep_def_merge_prop_impl              false
% 2.00/0.99  --prep_def_merge_mbd                    true
% 2.00/0.99  --prep_def_merge_tr_red                 false
% 2.00/0.99  --prep_def_merge_tr_cl                  false
% 2.00/0.99  --smt_preprocessing                     true
% 2.00/0.99  --smt_ac_axioms                         fast
% 2.00/0.99  --preprocessed_out                      false
% 2.00/0.99  --preprocessed_stats                    false
% 2.00/0.99  
% 2.00/0.99  ------ Abstraction refinement Options
% 2.00/0.99  
% 2.00/0.99  --abstr_ref                             []
% 2.00/0.99  --abstr_ref_prep                        false
% 2.00/0.99  --abstr_ref_until_sat                   false
% 2.00/0.99  --abstr_ref_sig_restrict                funpre
% 2.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/0.99  --abstr_ref_under                       []
% 2.00/0.99  
% 2.00/0.99  ------ SAT Options
% 2.00/0.99  
% 2.00/0.99  --sat_mode                              false
% 2.00/0.99  --sat_fm_restart_options                ""
% 2.00/0.99  --sat_gr_def                            false
% 2.00/0.99  --sat_epr_types                         true
% 2.00/0.99  --sat_non_cyclic_types                  false
% 2.00/0.99  --sat_finite_models                     false
% 2.00/0.99  --sat_fm_lemmas                         false
% 2.00/0.99  --sat_fm_prep                           false
% 2.00/0.99  --sat_fm_uc_incr                        true
% 2.00/0.99  --sat_out_model                         small
% 2.00/0.99  --sat_out_clauses                       false
% 2.00/0.99  
% 2.00/0.99  ------ QBF Options
% 2.00/0.99  
% 2.00/0.99  --qbf_mode                              false
% 2.00/0.99  --qbf_elim_univ                         false
% 2.00/0.99  --qbf_dom_inst                          none
% 2.00/0.99  --qbf_dom_pre_inst                      false
% 2.00/0.99  --qbf_sk_in                             false
% 2.00/0.99  --qbf_pred_elim                         true
% 2.00/0.99  --qbf_split                             512
% 2.00/0.99  
% 2.00/0.99  ------ BMC1 Options
% 2.00/0.99  
% 2.00/0.99  --bmc1_incremental                      false
% 2.00/0.99  --bmc1_axioms                           reachable_all
% 2.00/0.99  --bmc1_min_bound                        0
% 2.00/0.99  --bmc1_max_bound                        -1
% 2.00/0.99  --bmc1_max_bound_default                -1
% 2.00/0.99  --bmc1_symbol_reachability              true
% 2.00/0.99  --bmc1_property_lemmas                  false
% 2.00/0.99  --bmc1_k_induction                      false
% 2.00/0.99  --bmc1_non_equiv_states                 false
% 2.00/0.99  --bmc1_deadlock                         false
% 2.00/0.99  --bmc1_ucm                              false
% 2.00/0.99  --bmc1_add_unsat_core                   none
% 2.00/0.99  --bmc1_unsat_core_children              false
% 2.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/0.99  --bmc1_out_stat                         full
% 2.00/0.99  --bmc1_ground_init                      false
% 2.00/0.99  --bmc1_pre_inst_next_state              false
% 2.00/0.99  --bmc1_pre_inst_state                   false
% 2.00/0.99  --bmc1_pre_inst_reach_state             false
% 2.00/0.99  --bmc1_out_unsat_core                   false
% 2.00/0.99  --bmc1_aig_witness_out                  false
% 2.00/0.99  --bmc1_verbose                          false
% 2.00/0.99  --bmc1_dump_clauses_tptp                false
% 2.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.00/0.99  --bmc1_dump_file                        -
% 2.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.00/0.99  --bmc1_ucm_extend_mode                  1
% 2.00/0.99  --bmc1_ucm_init_mode                    2
% 2.00/0.99  --bmc1_ucm_cone_mode                    none
% 2.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.00/0.99  --bmc1_ucm_relax_model                  4
% 2.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/0.99  --bmc1_ucm_layered_model                none
% 2.00/0.99  --bmc1_ucm_max_lemma_size               10
% 2.00/0.99  
% 2.00/0.99  ------ AIG Options
% 2.00/0.99  
% 2.00/0.99  --aig_mode                              false
% 2.00/0.99  
% 2.00/0.99  ------ Instantiation Options
% 2.00/0.99  
% 2.00/0.99  --instantiation_flag                    true
% 2.00/0.99  --inst_sos_flag                         false
% 2.00/0.99  --inst_sos_phase                        true
% 2.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel_side                     none
% 2.00/0.99  --inst_solver_per_active                1400
% 2.00/0.99  --inst_solver_calls_frac                1.
% 2.00/0.99  --inst_passive_queue_type               priority_queues
% 2.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/0.99  --inst_passive_queues_freq              [25;2]
% 2.00/0.99  --inst_dismatching                      true
% 2.00/0.99  --inst_eager_unprocessed_to_passive     true
% 2.00/0.99  --inst_prop_sim_given                   true
% 2.00/0.99  --inst_prop_sim_new                     false
% 2.00/0.99  --inst_subs_new                         false
% 2.00/0.99  --inst_eq_res_simp                      false
% 2.00/0.99  --inst_subs_given                       false
% 2.00/0.99  --inst_orphan_elimination               true
% 2.00/0.99  --inst_learning_loop_flag               true
% 2.00/0.99  --inst_learning_start                   3000
% 2.00/0.99  --inst_learning_factor                  2
% 2.00/0.99  --inst_start_prop_sim_after_learn       3
% 2.00/0.99  --inst_sel_renew                        solver
% 2.00/0.99  --inst_lit_activity_flag                true
% 2.00/0.99  --inst_restr_to_given                   false
% 2.00/0.99  --inst_activity_threshold               500
% 2.00/0.99  --inst_out_proof                        true
% 2.00/0.99  
% 2.00/0.99  ------ Resolution Options
% 2.00/0.99  
% 2.00/0.99  --resolution_flag                       false
% 2.00/0.99  --res_lit_sel                           adaptive
% 2.00/0.99  --res_lit_sel_side                      none
% 2.00/0.99  --res_ordering                          kbo
% 2.00/0.99  --res_to_prop_solver                    active
% 2.00/0.99  --res_prop_simpl_new                    false
% 2.00/0.99  --res_prop_simpl_given                  true
% 2.00/0.99  --res_passive_queue_type                priority_queues
% 2.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/0.99  --res_passive_queues_freq               [15;5]
% 2.00/0.99  --res_forward_subs                      full
% 2.00/0.99  --res_backward_subs                     full
% 2.00/0.99  --res_forward_subs_resolution           true
% 2.00/0.99  --res_backward_subs_resolution          true
% 2.00/0.99  --res_orphan_elimination                true
% 2.00/0.99  --res_time_limit                        2.
% 2.00/0.99  --res_out_proof                         true
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Options
% 2.00/0.99  
% 2.00/0.99  --superposition_flag                    true
% 2.00/0.99  --sup_passive_queue_type                priority_queues
% 2.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.00/0.99  --demod_completeness_check              fast
% 2.00/0.99  --demod_use_ground                      true
% 2.00/0.99  --sup_to_prop_solver                    passive
% 2.00/0.99  --sup_prop_simpl_new                    true
% 2.00/0.99  --sup_prop_simpl_given                  true
% 2.00/0.99  --sup_fun_splitting                     false
% 2.00/0.99  --sup_smt_interval                      50000
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Simplification Setup
% 2.00/0.99  
% 2.00/0.99  --sup_indices_passive                   []
% 2.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_full_bw                           [BwDemod]
% 2.00/0.99  --sup_immed_triv                        [TrivRules]
% 2.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_immed_bw_main                     []
% 2.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  
% 2.00/0.99  ------ Combination Options
% 2.00/0.99  
% 2.00/0.99  --comb_res_mult                         3
% 2.00/0.99  --comb_sup_mult                         2
% 2.00/0.99  --comb_inst_mult                        10
% 2.00/0.99  
% 2.00/0.99  ------ Debug Options
% 2.00/0.99  
% 2.00/0.99  --dbg_backtrace                         false
% 2.00/0.99  --dbg_dump_prop_clauses                 false
% 2.00/0.99  --dbg_dump_prop_clauses_file            -
% 2.00/0.99  --dbg_out_stat                          false
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  ------ Proving...
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.00/0.99  
% 2.00/0.99  % SZS output start Saturation for theBenchmark.p
% 2.00/0.99  
% 2.00/0.99  fof(f13,axiom,(
% 2.00/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f34,plain,(
% 2.00/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.00/0.99    inference(ennf_transformation,[],[f13])).
% 2.00/0.99  
% 2.00/0.99  fof(f35,plain,(
% 2.00/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.00/0.99    inference(flattening,[],[f34])).
% 2.00/0.99  
% 2.00/0.99  fof(f69,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f35])).
% 2.00/0.99  
% 2.00/0.99  fof(f5,axiom,(
% 2.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f26,plain,(
% 2.00/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.99    inference(ennf_transformation,[],[f5])).
% 2.00/0.99  
% 2.00/0.99  fof(f54,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.99    inference(cnf_transformation,[],[f26])).
% 2.00/0.99  
% 2.00/0.99  fof(f2,axiom,(
% 2.00/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f20,plain,(
% 2.00/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f2])).
% 2.00/1.00  
% 2.00/1.00  fof(f21,plain,(
% 2.00/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.00/1.00    inference(flattening,[],[f20])).
% 2.00/1.00  
% 2.00/1.00  fof(f49,plain,(
% 2.00/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f21])).
% 2.00/1.00  
% 2.00/1.00  fof(f70,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f35])).
% 2.00/1.00  
% 2.00/1.00  fof(f71,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f35])).
% 2.00/1.00  
% 2.00/1.00  fof(f4,axiom,(
% 2.00/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f24,plain,(
% 2.00/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f4])).
% 2.00/1.00  
% 2.00/1.00  fof(f25,plain,(
% 2.00/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.00/1.00    inference(flattening,[],[f24])).
% 2.00/1.00  
% 2.00/1.00  fof(f53,plain,(
% 2.00/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f25])).
% 2.00/1.00  
% 2.00/1.00  fof(f3,axiom,(
% 2.00/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f22,plain,(
% 2.00/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f3])).
% 2.00/1.00  
% 2.00/1.00  fof(f23,plain,(
% 2.00/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.00/1.00    inference(flattening,[],[f22])).
% 2.00/1.00  
% 2.00/1.00  fof(f51,plain,(
% 2.00/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f23])).
% 2.00/1.00  
% 2.00/1.00  fof(f12,axiom,(
% 2.00/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f68,plain,(
% 2.00/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f12])).
% 2.00/1.00  
% 2.00/1.00  fof(f83,plain,(
% 2.00/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(definition_unfolding,[],[f51,f68])).
% 2.00/1.00  
% 2.00/1.00  fof(f52,plain,(
% 2.00/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f23])).
% 2.00/1.00  
% 2.00/1.00  fof(f82,plain,(
% 2.00/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(definition_unfolding,[],[f52,f68])).
% 2.00/1.00  
% 2.00/1.00  fof(f48,plain,(
% 2.00/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f21])).
% 2.00/1.00  
% 2.00/1.00  fof(f50,plain,(
% 2.00/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f21])).
% 2.00/1.00  
% 2.00/1.00  fof(f11,axiom,(
% 2.00/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f67,plain,(
% 2.00/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f11])).
% 2.00/1.00  
% 2.00/1.00  fof(f7,axiom,(
% 2.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f28,plain,(
% 2.00/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/1.00    inference(ennf_transformation,[],[f7])).
% 2.00/1.00  
% 2.00/1.00  fof(f56,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f28])).
% 2.00/1.00  
% 2.00/1.00  fof(f6,axiom,(
% 2.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f19,plain,(
% 2.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.00/1.00    inference(pure_predicate_removal,[],[f6])).
% 2.00/1.00  
% 2.00/1.00  fof(f27,plain,(
% 2.00/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/1.00    inference(ennf_transformation,[],[f19])).
% 2.00/1.00  
% 2.00/1.00  fof(f55,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f27])).
% 2.00/1.00  
% 2.00/1.00  fof(f10,axiom,(
% 2.00/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f32,plain,(
% 2.00/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.00/1.00    inference(ennf_transformation,[],[f10])).
% 2.00/1.00  
% 2.00/1.00  fof(f33,plain,(
% 2.00/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/1.00    inference(flattening,[],[f32])).
% 2.00/1.00  
% 2.00/1.00  fof(f42,plain,(
% 2.00/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/1.00    inference(nnf_transformation,[],[f33])).
% 2.00/1.00  
% 2.00/1.00  fof(f64,plain,(
% 2.00/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f42])).
% 2.00/1.00  
% 2.00/1.00  fof(f66,plain,(
% 2.00/1.00    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f11])).
% 2.00/1.00  
% 2.00/1.00  fof(f16,conjecture,(
% 2.00/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f17,negated_conjecture,(
% 2.00/1.00    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 2.00/1.00    inference(negated_conjecture,[],[f16])).
% 2.00/1.00  
% 2.00/1.00  fof(f18,plain,(
% 2.00/1.00    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 2.00/1.00    inference(pure_predicate_removal,[],[f17])).
% 2.00/1.00  
% 2.00/1.00  fof(f39,plain,(
% 2.00/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f18])).
% 2.00/1.00  
% 2.00/1.00  fof(f40,plain,(
% 2.00/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 2.00/1.00    inference(flattening,[],[f39])).
% 2.00/1.00  
% 2.00/1.00  fof(f45,plain,(
% 2.00/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.00/1.00    introduced(choice_axiom,[])).
% 2.00/1.00  
% 2.00/1.00  fof(f44,plain,(
% 2.00/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1))) )),
% 2.00/1.00    introduced(choice_axiom,[])).
% 2.00/1.00  
% 2.00/1.00  fof(f43,plain,(
% 2.00/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.00/1.00    introduced(choice_axiom,[])).
% 2.00/1.00  
% 2.00/1.00  fof(f46,plain,(
% 2.00/1.00    (((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f45,f44,f43])).
% 2.00/1.00  
% 2.00/1.00  fof(f80,plain,(
% 2.00/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f9,axiom,(
% 2.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f30,plain,(
% 2.00/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/1.00    inference(ennf_transformation,[],[f9])).
% 2.00/1.00  
% 2.00/1.00  fof(f31,plain,(
% 2.00/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/1.00    inference(flattening,[],[f30])).
% 2.00/1.00  
% 2.00/1.00  fof(f41,plain,(
% 2.00/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/1.00    inference(nnf_transformation,[],[f31])).
% 2.00/1.00  
% 2.00/1.00  fof(f58,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f41])).
% 2.00/1.00  
% 2.00/1.00  fof(f79,plain,(
% 2.00/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f76,plain,(
% 2.00/1.00    ~v2_struct_0(sK1)),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f1,axiom,(
% 2.00/1.00    v1_xboole_0(k1_xboole_0)),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f47,plain,(
% 2.00/1.00    v1_xboole_0(k1_xboole_0)),
% 2.00/1.00    inference(cnf_transformation,[],[f1])).
% 2.00/1.00  
% 2.00/1.00  fof(f14,axiom,(
% 2.00/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f36,plain,(
% 2.00/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f14])).
% 2.00/1.00  
% 2.00/1.00  fof(f37,plain,(
% 2.00/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.00/1.00    inference(flattening,[],[f36])).
% 2.00/1.00  
% 2.00/1.00  fof(f72,plain,(
% 2.00/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f37])).
% 2.00/1.00  
% 2.00/1.00  fof(f15,axiom,(
% 2.00/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f38,plain,(
% 2.00/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.00/1.00    inference(ennf_transformation,[],[f15])).
% 2.00/1.00  
% 2.00/1.00  fof(f73,plain,(
% 2.00/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f38])).
% 2.00/1.00  
% 2.00/1.00  fof(f77,plain,(
% 2.00/1.00    l1_orders_2(sK1)),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f75,plain,(
% 2.00/1.00    l1_orders_2(sK0)),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f74,plain,(
% 2.00/1.00    ~v2_struct_0(sK0)),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f81,plain,(
% 2.00/1.00    k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f78,plain,(
% 2.00/1.00    v1_funct_1(sK2)),
% 2.00/1.00    inference(cnf_transformation,[],[f46])).
% 2.00/1.00  
% 2.00/1.00  fof(f60,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f41])).
% 2.00/1.00  
% 2.00/1.00  fof(f8,axiom,(
% 2.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f29,plain,(
% 2.00/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/1.00    inference(ennf_transformation,[],[f8])).
% 2.00/1.00  
% 2.00/1.00  fof(f57,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f29])).
% 2.00/1.00  
% 2.00/1.00  cnf(c_353,plain,
% 2.00/1.00      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_352,plain,
% 2.00/1.00      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_350,plain,
% 2.00/1.00      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_349,plain,
% 2.00/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.00/1.00      | v1_funct_2(X3,X4,X5)
% 2.00/1.00      | X3 != X0
% 2.00/1.00      | X4 != X1
% 2.00/1.00      | X5 != X2 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_347,plain,
% 2.00/1.00      ( ~ v4_relat_1(X0,X1) | v4_relat_1(X0,X2) | X2 != X1 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_340,plain,
% 2.00/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_339,plain,
% 2.00/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_338,plain,
% 2.00/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_336,plain,
% 2.00/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.00/1.00      theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1347,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_23,plain,
% 2.00/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.00/1.00      | ~ v2_funct_1(X0)
% 2.00/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.00/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_7,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2,plain,
% 2.00/1.00      ( ~ v1_relat_1(X0)
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.00/1.00      | ~ v2_funct_1(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_197,plain,
% 2.00/1.00      ( ~ v2_funct_1(X0)
% 2.00/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.00/1.00      inference(global_propositional_subsumption,[status(thm)],[c_23,c_7,c_2]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_198,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.00/1.00      | ~ v2_funct_1(X0) ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_197]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_22,plain,
% 2.00/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.00/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ v2_funct_1(X0)
% 2.00/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.00/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_21,plain,
% 2.00/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ v2_funct_1(X0)
% 2.00/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.00/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_6,plain,
% 2.00/1.00      ( ~ v1_relat_1(X0)
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ v2_funct_1(X0)
% 2.00/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.00/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_5,plain,
% 2.00/1.00      ( ~ v1_relat_1(X0)
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ v2_funct_1(X0)
% 2.00/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_4,plain,
% 2.00/1.00      ( ~ v1_relat_1(X0)
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ v2_funct_1(X0)
% 2.00/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_3,plain,
% 2.00/1.00      ( ~ v1_relat_1(X0)
% 2.00/1.00      | v1_relat_1(k2_funct_1(X0))
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ v2_funct_1(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1,plain,
% 2.00/1.00      ( ~ v1_relat_1(X0)
% 2.00/1.00      | ~ v1_funct_1(X0)
% 2.00/1.00      | ~ v2_funct_1(X0)
% 2.00/1.00      | v2_funct_1(k2_funct_1(X0)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_19,plain,
% 2.00/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1489,plain,
% 2.00/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_9,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1491,plain,
% 2.00/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.00/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1748,plain,
% 2.00/1.00      ( k1_relset_1(X0,X0,k6_partfun1(X0)) = k1_relat_1(k6_partfun1(X0)) ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_1489,c_1491]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_8,plain,
% 2.00/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_18,plain,
% 2.00/1.00      ( ~ v1_partfun1(X0,X1)
% 2.00/1.00      | ~ v4_relat_1(X0,X1)
% 2.00/1.00      | ~ v1_relat_1(X0)
% 2.00/1.00      | k1_relat_1(X0) = X1 ),
% 2.00/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_491,plain,
% 2.00/1.00      ( ~ v1_partfun1(X0,X1)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | ~ v1_relat_1(X0)
% 2.00/1.00      | k1_relat_1(X0) = X1 ),
% 2.00/1.00      inference(resolution,[status(thm)],[c_8,c_18]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_495,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | ~ v1_partfun1(X0,X1)
% 2.00/1.00      | k1_relat_1(X0) = X1 ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_491,c_18,c_8,c_7]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_496,plain,
% 2.00/1.00      ( ~ v1_partfun1(X0,X1)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | k1_relat_1(X0) = X1 ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_495]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_20,plain,
% 2.00/1.00      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_537,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | X3 != X1
% 2.00/1.00      | k1_relat_1(X0) = X1
% 2.00/1.00      | k6_partfun1(X3) != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_496,c_20]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_538,plain,
% 2.00/1.00      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.00/1.00      | k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_537]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1487,plain,
% 2.00/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0
% 2.00/1.00      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1683,plain,
% 2.00/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_1489,c_1487]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2182,plain,
% 2.00/1.00      ( k1_relset_1(X0,X0,k6_partfun1(X0)) = X0 ),
% 2.00/1.00      inference(light_normalisation,[status(thm)],[c_1748,c_1683]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_27,negated_conjecture,
% 2.00/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1488,plain,
% 2.00/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1749,plain,
% 2.00/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_1488,c_1491]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_16,plain,
% 2.00/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.00/1.00      | k1_xboole_0 = X2 ),
% 2.00/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_28,negated_conjecture,
% 2.00/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_957,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.00/1.00      | u1_struct_0(sK1) != X2
% 2.00/1.00      | u1_struct_0(sK0) != X1
% 2.00/1.00      | sK2 != X0
% 2.00/1.00      | k1_xboole_0 = X2 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_958,plain,
% 2.00/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.00/1.00      | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 2.00/1.00      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_957]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_960,plain,
% 2.00/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 2.00/1.00      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.00/1.00      inference(global_propositional_subsumption,[status(thm)],[c_958,c_27]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1882,plain,
% 2.00/1.00      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1749,c_960]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_31,negated_conjecture,
% 2.00/1.00      ( ~ v2_struct_0(sK1) ),
% 2.00/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_0,plain,
% 2.00/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_24,plain,
% 2.00/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_379,plain,
% 2.00/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_25,plain,
% 2.00/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_30,negated_conjecture,
% 2.00/1.00      ( l1_orders_2(sK1) ),
% 2.00/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_397,plain,
% 2.00/1.00      ( l1_struct_0(X0) | sK1 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_398,plain,
% 2.00/1.00      ( l1_struct_0(sK1) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_435,plain,
% 2.00/1.00      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_379,c_398]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_436,plain,
% 2.00/1.00      ( v2_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1934,plain,
% 2.00/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_1882,c_31,c_436]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1942,plain,
% 2.00/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1934,c_1488]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_32,negated_conjecture,
% 2.00/1.00      ( l1_orders_2(sK0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_404,plain,
% 2.00/1.00      ( l1_struct_0(X0) | sK0 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_405,plain,
% 2.00/1.00      ( l1_struct_0(sK0) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_404]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_443,plain,
% 2.00/1.00      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK0 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_379,c_405]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_444,plain,
% 2.00/1.00      ( v2_struct_0(sK0) | u1_struct_0(sK0) != k1_xboole_0 ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_443]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_33,negated_conjecture,
% 2.00/1.00      ( ~ v2_struct_0(sK0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_446,plain,
% 2.00/1.00      ( u1_struct_0(sK0) != k1_xboole_0 ),
% 2.00/1.00      inference(global_propositional_subsumption,[status(thm)],[c_444,c_33]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1941,plain,
% 2.00/1.00      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1934,c_446]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_26,negated_conjecture,
% 2.00/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.00/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.00/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_29,negated_conjecture,
% 2.00/1.00      ( v1_funct_1(sK2) ),
% 2.00/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_415,plain,
% 2.00/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.00/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != sK2 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_968,plain,
% 2.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.00/1.00      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != sK2 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_415,c_28]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1485,plain,
% 2.00/1.00      ( u1_struct_0(sK1) != u1_struct_0(sK0)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_968]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1940,plain,
% 2.00/1.00      ( u1_struct_0(sK1) != k1_relat_1(sK2)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) != iProver_top ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1934,c_1485]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_14,plain,
% 2.00/1.00      ( v1_funct_2(X0,X1,X2)
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.00/1.00      | k1_xboole_0 = X2 ),
% 2.00/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_938,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.00/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.00/1.00      | u1_struct_0(sK1) != X1
% 2.00/1.00      | u1_struct_0(sK0) != X2
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != X0
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | k1_xboole_0 = X2 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_415]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_939,plain,
% 2.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.00/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | k1_xboole_0 = u1_struct_0(sK0) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_938]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1486,plain,
% 2.00/1.00      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | k1_xboole_0 = u1_struct_0(sK0)
% 2.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_940,plain,
% 2.00/1.00      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | k1_xboole_0 = u1_struct_0(sK0)
% 2.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1349,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1556,plain,
% 2.00/1.00      ( u1_struct_0(sK0) != X0
% 2.00/1.00      | u1_struct_0(sK0) = k1_xboole_0
% 2.00/1.00      | k1_xboole_0 != X0 ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1349]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1612,plain,
% 2.00/1.00      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.00/1.00      | u1_struct_0(sK0) = k1_xboole_0
% 2.00/1.00      | k1_xboole_0 != u1_struct_0(sK0) ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1556]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1348,plain,( X0 = X0 ),theory(equality) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1613,plain,
% 2.00/1.00      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1348]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1630,plain,
% 2.00/1.00      ( k2_funct_1(sK2) != sK2
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
% 2.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_1486,c_33,c_444,c_940,c_1612,c_1613]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1631,plain,
% 2.00/1.00      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != u1_struct_0(sK1)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_1630]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1939,plain,
% 2.00/1.00      ( k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != u1_struct_0(sK1)
% 2.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.00/1.00      | k2_funct_1(sK2) != sK2
% 2.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) != iProver_top ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1934,c_1631]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_10,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.00/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1490,plain,
% 2.00/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.00/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1739,plain,
% 2.00/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_1488,c_1490]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1938,plain,
% 2.00/1.00      ( k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1934,c_1739]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1937,plain,
% 2.00/1.00      ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1934,c_1749]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1738,plain,
% 2.00/1.00      ( k2_relset_1(X0,X0,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0)) ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_1489,c_1490]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_438,plain,
% 2.00/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.00/1.00      inference(global_propositional_subsumption,[status(thm)],[c_436,c_31]) ).
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  % SZS output end Saturation for theBenchmark.p
% 2.00/1.00  
% 2.00/1.00  ------                               Statistics
% 2.00/1.00  
% 2.00/1.00  ------ General
% 2.00/1.00  
% 2.00/1.00  abstr_ref_over_cycles:                  0
% 2.00/1.00  abstr_ref_under_cycles:                 0
% 2.00/1.00  gc_basic_clause_elim:                   0
% 2.00/1.00  forced_gc_time:                         0
% 2.00/1.00  parsing_time:                           0.023
% 2.00/1.00  unif_index_cands_time:                  0.
% 2.00/1.00  unif_index_add_time:                    0.
% 2.00/1.00  orderings_time:                         0.
% 2.00/1.00  out_proof_time:                         0.
% 2.00/1.00  total_time:                             0.149
% 2.00/1.00  num_of_symbols:                         56
% 2.00/1.00  num_of_terms:                           1900
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing
% 2.00/1.00  
% 2.00/1.00  num_of_splits:                          0
% 2.00/1.00  num_of_split_atoms:                     0
% 2.00/1.00  num_of_reused_defs:                     0
% 2.00/1.00  num_eq_ax_congr_red:                    16
% 2.00/1.00  num_of_sem_filtered_clauses:            10
% 2.00/1.00  num_of_subtypes:                        0
% 2.00/1.00  monotx_restored_types:                  0
% 2.00/1.00  sat_num_of_epr_types:                   0
% 2.00/1.00  sat_num_of_non_cyclic_types:            0
% 2.00/1.00  sat_guarded_non_collapsed_types:        0
% 2.00/1.00  num_pure_diseq_elim:                    0
% 2.00/1.00  simp_replaced_by:                       0
% 2.00/1.00  res_preprocessed:                       85
% 2.00/1.00  prep_upred:                             0
% 2.00/1.00  prep_unflattend:                        65
% 2.00/1.00  smt_new_axioms:                         0
% 2.00/1.00  pred_elim_cands:                        1
% 2.00/1.00  pred_elim:                              9
% 2.00/1.00  pred_elim_cl:                           15
% 2.00/1.00  pred_elim_cycles:                       13
% 2.00/1.00  merged_defs:                            0
% 2.00/1.00  merged_defs_ncl:                        0
% 2.00/1.00  bin_hyper_res:                          0
% 2.00/1.00  prep_cycles:                            4
% 2.00/1.00  pred_elim_time:                         0.023
% 2.00/1.00  splitting_time:                         0.
% 2.00/1.00  sem_filter_time:                        0.
% 2.00/1.00  monotx_time:                            0.
% 2.00/1.00  subtype_inf_time:                       0.
% 2.00/1.00  
% 2.00/1.00  ------ Problem properties
% 2.00/1.00  
% 2.00/1.00  clauses:                                10
% 2.00/1.00  conjectures:                            1
% 2.00/1.00  epr:                                    0
% 2.00/1.00  horn:                                   9
% 2.00/1.00  ground:                                 6
% 2.00/1.00  unary:                                  4
% 2.00/1.00  binary:                                 4
% 2.00/1.00  lits:                                   21
% 2.00/1.00  lits_eq:                                14
% 2.00/1.00  fd_pure:                                0
% 2.00/1.00  fd_pseudo:                              0
% 2.00/1.00  fd_cond:                                0
% 2.00/1.00  fd_pseudo_cond:                         0
% 2.00/1.00  ac_symbols:                             0
% 2.00/1.00  
% 2.00/1.00  ------ Propositional Solver
% 2.00/1.00  
% 2.00/1.00  prop_solver_calls:                      27
% 2.00/1.00  prop_fast_solver_calls:                 671
% 2.00/1.00  smt_solver_calls:                       0
% 2.00/1.00  smt_fast_solver_calls:                  0
% 2.00/1.00  prop_num_of_clauses:                    610
% 2.00/1.00  prop_preprocess_simplified:             2457
% 2.00/1.00  prop_fo_subsumed:                       12
% 2.00/1.00  prop_solver_time:                       0.
% 2.00/1.00  smt_solver_time:                        0.
% 2.00/1.00  smt_fast_solver_time:                   0.
% 2.00/1.00  prop_fast_solver_time:                  0.
% 2.00/1.00  prop_unsat_core_time:                   0.
% 2.00/1.00  
% 2.00/1.00  ------ QBF
% 2.00/1.00  
% 2.00/1.00  qbf_q_res:                              0
% 2.00/1.00  qbf_num_tautologies:                    0
% 2.00/1.00  qbf_prep_cycles:                        0
% 2.00/1.00  
% 2.00/1.00  ------ BMC1
% 2.00/1.00  
% 2.00/1.00  bmc1_current_bound:                     -1
% 2.00/1.00  bmc1_last_solved_bound:                 -1
% 2.00/1.00  bmc1_unsat_core_size:                   -1
% 2.00/1.00  bmc1_unsat_core_parents_size:           -1
% 2.00/1.00  bmc1_merge_next_fun:                    0
% 2.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.00/1.00  
% 2.00/1.00  ------ Instantiation
% 2.00/1.00  
% 2.00/1.00  inst_num_of_clauses:                    175
% 2.00/1.00  inst_num_in_passive:                    22
% 2.00/1.00  inst_num_in_active:                     114
% 2.00/1.00  inst_num_in_unprocessed:                40
% 2.00/1.00  inst_num_of_loops:                      120
% 2.00/1.00  inst_num_of_learning_restarts:          0
% 2.00/1.00  inst_num_moves_active_passive:          3
% 2.00/1.00  inst_lit_activity:                      0
% 2.00/1.00  inst_lit_activity_moves:                0
% 2.00/1.00  inst_num_tautologies:                   0
% 2.00/1.00  inst_num_prop_implied:                  0
% 2.00/1.00  inst_num_existing_simplified:           0
% 2.00/1.00  inst_num_eq_res_simplified:             0
% 2.00/1.00  inst_num_child_elim:                    0
% 2.00/1.00  inst_num_of_dismatching_blockings:      22
% 2.00/1.00  inst_num_of_non_proper_insts:           141
% 2.00/1.00  inst_num_of_duplicates:                 0
% 2.00/1.00  inst_inst_num_from_inst_to_res:         0
% 2.00/1.00  inst_dismatching_checking_time:         0.
% 2.00/1.00  
% 2.00/1.00  ------ Resolution
% 2.00/1.00  
% 2.00/1.00  res_num_of_clauses:                     0
% 2.00/1.00  res_num_in_passive:                     0
% 2.00/1.00  res_num_in_active:                      0
% 2.00/1.00  res_num_of_loops:                       89
% 2.00/1.00  res_forward_subset_subsumed:            35
% 2.00/1.00  res_backward_subset_subsumed:           2
% 2.00/1.00  res_forward_subsumed:                   0
% 2.00/1.00  res_backward_subsumed:                  0
% 2.00/1.00  res_forward_subsumption_resolution:     1
% 2.00/1.00  res_backward_subsumption_resolution:    0
% 2.00/1.00  res_clause_to_clause_subsumption:       34
% 2.00/1.00  res_orphan_elimination:                 0
% 2.00/1.00  res_tautology_del:                      35
% 2.00/1.00  res_num_eq_res_simplified:              0
% 2.00/1.00  res_num_sel_changes:                    0
% 2.00/1.00  res_moves_from_active_to_pass:          0
% 2.00/1.00  
% 2.00/1.00  ------ Superposition
% 2.00/1.00  
% 2.00/1.00  sup_time_total:                         0.
% 2.00/1.00  sup_time_generating:                    0.
% 2.00/1.00  sup_time_sim_full:                      0.
% 2.00/1.00  sup_time_sim_immed:                     0.
% 2.00/1.00  
% 2.00/1.00  sup_num_of_clauses:                     14
% 2.00/1.00  sup_num_in_active:                      14
% 2.00/1.00  sup_num_in_passive:                     0
% 2.00/1.00  sup_num_of_loops:                       22
% 2.00/1.00  sup_fw_superposition:                   5
% 2.00/1.00  sup_bw_superposition:                   2
% 2.00/1.00  sup_immediate_simplified:               1
% 2.00/1.00  sup_given_eliminated:                   0
% 2.00/1.00  comparisons_done:                       0
% 2.00/1.00  comparisons_avoided:                    0
% 2.00/1.00  
% 2.00/1.00  ------ Simplifications
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  sim_fw_subset_subsumed:                 0
% 2.00/1.00  sim_bw_subset_subsumed:                 2
% 2.00/1.00  sim_fw_subsumed:                        0
% 2.00/1.00  sim_bw_subsumed:                        0
% 2.00/1.00  sim_fw_subsumption_res:                 0
% 2.00/1.00  sim_bw_subsumption_res:                 0
% 2.00/1.00  sim_tautology_del:                      0
% 2.00/1.00  sim_eq_tautology_del:                   0
% 2.00/1.00  sim_eq_res_simp:                        0
% 2.00/1.00  sim_fw_demodulated:                     0
% 2.00/1.00  sim_bw_demodulated:                     7
% 2.00/1.00  sim_light_normalised:                   1
% 2.00/1.00  sim_joinable_taut:                      0
% 2.00/1.00  sim_joinable_simp:                      0
% 2.00/1.00  sim_ac_normalised:                      0
% 2.00/1.00  sim_smt_subsumption:                    0
% 2.00/1.00  
%------------------------------------------------------------------------------
