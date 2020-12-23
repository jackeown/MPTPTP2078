%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:16 EST 2020

% Result     : CounterSatisfiable 1.71s
% Output     : Saturation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 842 expanded)
%              Number of clauses        :   87 ( 247 expanded)
%              Number of leaves         :   27 ( 229 expanded)
%              Depth                    :   17
%              Number of atoms          :  610 (6509 expanded)
%              Number of equality atoms :  216 (1076 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39,f38])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f37,plain,(
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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_471,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_472,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_185,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_11,c_1])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_408,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_186,c_25])).

cnf(c_409,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_413,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_27])).

cnf(c_331,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_330,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_328,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_320,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_319,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_318,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_316,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_313,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_462,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_463,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_730,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_791,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_730])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_426,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_427,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_648,plain,
    ( k1_relset_1(X0,X1,sK2) = X0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_427])).

cnf(c_649,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_727,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_649])).

cnf(c_833,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_791,c_727])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_354,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_23,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_372,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_373,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_390,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_354,c_373])).

cnf(c_391,plain,
    ( v2_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_393,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_29])).

cnf(c_732,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_867,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_732])).

cnf(c_874,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_867,c_730])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_548,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_25])).

cnf(c_555,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_548,c_413])).

cnf(c_616,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_555,c_26])).

cnf(c_729,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_616])).

cnf(c_873,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_867,c_729])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_379,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_380,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_398,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_354,c_380])).

cnf(c_399,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_401,plain,
    ( u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_31])).

cnf(c_731,plain,
    ( u1_struct_0(sK0) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_872,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_867,c_731])).

cnf(c_871,plain,
    ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_867,c_791])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_444,plain,
    ( v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_445,plain,
    ( v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_629,plain,
    ( k1_relset_1(X0,X1,sK2) != X0
    | u1_struct_0(sK1) != X0
    | u1_struct_0(sK0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_555,c_445])).

cnf(c_630,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_728,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_630])).

cnf(c_737,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_798,plain,
    ( u1_struct_0(sK0) != X0_50
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != X0_50 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_807,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_733,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_808,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_861,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_funct_1(sK2) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_731,c_807,c_808])).

cnf(c_862,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_861])).

cnf(c_870,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_867,c_862])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 1.71/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.71/0.99  
% 1.71/0.99  ------  iProver source info
% 1.71/0.99  
% 1.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.71/0.99  git: non_committed_changes: false
% 1.71/0.99  git: last_make_outside_of_git: false
% 1.71/0.99  
% 1.71/0.99  ------ 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options
% 1.71/0.99  
% 1.71/0.99  --out_options                           all
% 1.71/0.99  --tptp_safe_out                         true
% 1.71/0.99  --problem_path                          ""
% 1.71/0.99  --include_path                          ""
% 1.71/0.99  --clausifier                            res/vclausify_rel
% 1.71/0.99  --clausifier_options                    --mode clausify
% 1.71/0.99  --stdin                                 false
% 1.71/0.99  --stats_out                             all
% 1.71/0.99  
% 1.71/0.99  ------ General Options
% 1.71/0.99  
% 1.71/0.99  --fof                                   false
% 1.71/0.99  --time_out_real                         305.
% 1.71/0.99  --time_out_virtual                      -1.
% 1.71/0.99  --symbol_type_check                     false
% 1.71/0.99  --clausify_out                          false
% 1.71/0.99  --sig_cnt_out                           false
% 1.71/0.99  --trig_cnt_out                          false
% 1.71/0.99  --trig_cnt_out_tolerance                1.
% 1.71/0.99  --trig_cnt_out_sk_spl                   false
% 1.71/0.99  --abstr_cl_out                          false
% 1.71/0.99  
% 1.71/0.99  ------ Global Options
% 1.71/0.99  
% 1.71/0.99  --schedule                              default
% 1.71/0.99  --add_important_lit                     false
% 1.71/0.99  --prop_solver_per_cl                    1000
% 1.71/0.99  --min_unsat_core                        false
% 1.71/0.99  --soft_assumptions                      false
% 1.71/0.99  --soft_lemma_size                       3
% 1.71/0.99  --prop_impl_unit_size                   0
% 1.71/0.99  --prop_impl_unit                        []
% 1.71/0.99  --share_sel_clauses                     true
% 1.71/0.99  --reset_solvers                         false
% 1.71/0.99  --bc_imp_inh                            [conj_cone]
% 1.71/0.99  --conj_cone_tolerance                   3.
% 1.71/0.99  --extra_neg_conj                        none
% 1.71/0.99  --large_theory_mode                     true
% 1.71/0.99  --prolific_symb_bound                   200
% 1.71/0.99  --lt_threshold                          2000
% 1.71/0.99  --clause_weak_htbl                      true
% 1.71/0.99  --gc_record_bc_elim                     false
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing Options
% 1.71/0.99  
% 1.71/0.99  --preprocessing_flag                    true
% 1.71/0.99  --time_out_prep_mult                    0.1
% 1.71/0.99  --splitting_mode                        input
% 1.71/0.99  --splitting_grd                         true
% 1.71/0.99  --splitting_cvd                         false
% 1.71/0.99  --splitting_cvd_svl                     false
% 1.71/0.99  --splitting_nvd                         32
% 1.71/0.99  --sub_typing                            true
% 1.71/0.99  --prep_gs_sim                           true
% 1.71/0.99  --prep_unflatten                        true
% 1.71/0.99  --prep_res_sim                          true
% 1.71/0.99  --prep_upred                            true
% 1.71/0.99  --prep_sem_filter                       exhaustive
% 1.71/0.99  --prep_sem_filter_out                   false
% 1.71/0.99  --pred_elim                             true
% 1.71/0.99  --res_sim_input                         true
% 1.71/0.99  --eq_ax_congr_red                       true
% 1.71/0.99  --pure_diseq_elim                       true
% 1.71/0.99  --brand_transform                       false
% 1.71/0.99  --non_eq_to_eq                          false
% 1.71/0.99  --prep_def_merge                        true
% 1.71/0.99  --prep_def_merge_prop_impl              false
% 1.71/0.99  --prep_def_merge_mbd                    true
% 1.71/0.99  --prep_def_merge_tr_red                 false
% 1.71/0.99  --prep_def_merge_tr_cl                  false
% 1.71/0.99  --smt_preprocessing                     true
% 1.71/0.99  --smt_ac_axioms                         fast
% 1.71/0.99  --preprocessed_out                      false
% 1.71/0.99  --preprocessed_stats                    false
% 1.71/0.99  
% 1.71/0.99  ------ Abstraction refinement Options
% 1.71/0.99  
% 1.71/0.99  --abstr_ref                             []
% 1.71/0.99  --abstr_ref_prep                        false
% 1.71/0.99  --abstr_ref_until_sat                   false
% 1.71/0.99  --abstr_ref_sig_restrict                funpre
% 1.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.99  --abstr_ref_under                       []
% 1.71/0.99  
% 1.71/0.99  ------ SAT Options
% 1.71/0.99  
% 1.71/0.99  --sat_mode                              false
% 1.71/0.99  --sat_fm_restart_options                ""
% 1.71/0.99  --sat_gr_def                            false
% 1.71/0.99  --sat_epr_types                         true
% 1.71/0.99  --sat_non_cyclic_types                  false
% 1.71/0.99  --sat_finite_models                     false
% 1.71/0.99  --sat_fm_lemmas                         false
% 1.71/0.99  --sat_fm_prep                           false
% 1.71/0.99  --sat_fm_uc_incr                        true
% 1.71/0.99  --sat_out_model                         small
% 1.71/0.99  --sat_out_clauses                       false
% 1.71/0.99  
% 1.71/0.99  ------ QBF Options
% 1.71/0.99  
% 1.71/0.99  --qbf_mode                              false
% 1.71/0.99  --qbf_elim_univ                         false
% 1.71/0.99  --qbf_dom_inst                          none
% 1.71/0.99  --qbf_dom_pre_inst                      false
% 1.71/0.99  --qbf_sk_in                             false
% 1.71/0.99  --qbf_pred_elim                         true
% 1.71/0.99  --qbf_split                             512
% 1.71/0.99  
% 1.71/0.99  ------ BMC1 Options
% 1.71/0.99  
% 1.71/0.99  --bmc1_incremental                      false
% 1.71/0.99  --bmc1_axioms                           reachable_all
% 1.71/0.99  --bmc1_min_bound                        0
% 1.71/0.99  --bmc1_max_bound                        -1
% 1.71/0.99  --bmc1_max_bound_default                -1
% 1.71/0.99  --bmc1_symbol_reachability              true
% 1.71/0.99  --bmc1_property_lemmas                  false
% 1.71/0.99  --bmc1_k_induction                      false
% 1.71/0.99  --bmc1_non_equiv_states                 false
% 1.71/0.99  --bmc1_deadlock                         false
% 1.71/0.99  --bmc1_ucm                              false
% 1.71/0.99  --bmc1_add_unsat_core                   none
% 1.71/0.99  --bmc1_unsat_core_children              false
% 1.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.99  --bmc1_out_stat                         full
% 1.71/0.99  --bmc1_ground_init                      false
% 1.71/0.99  --bmc1_pre_inst_next_state              false
% 1.71/0.99  --bmc1_pre_inst_state                   false
% 1.71/0.99  --bmc1_pre_inst_reach_state             false
% 1.71/0.99  --bmc1_out_unsat_core                   false
% 1.71/0.99  --bmc1_aig_witness_out                  false
% 1.71/0.99  --bmc1_verbose                          false
% 1.71/0.99  --bmc1_dump_clauses_tptp                false
% 1.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.99  --bmc1_dump_file                        -
% 1.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.99  --bmc1_ucm_extend_mode                  1
% 1.71/0.99  --bmc1_ucm_init_mode                    2
% 1.71/0.99  --bmc1_ucm_cone_mode                    none
% 1.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.99  --bmc1_ucm_relax_model                  4
% 1.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.99  --bmc1_ucm_layered_model                none
% 1.71/0.99  --bmc1_ucm_max_lemma_size               10
% 1.71/0.99  
% 1.71/0.99  ------ AIG Options
% 1.71/0.99  
% 1.71/0.99  --aig_mode                              false
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation Options
% 1.71/0.99  
% 1.71/0.99  --instantiation_flag                    true
% 1.71/0.99  --inst_sos_flag                         false
% 1.71/0.99  --inst_sos_phase                        true
% 1.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel_side                     num_symb
% 1.71/0.99  --inst_solver_per_active                1400
% 1.71/0.99  --inst_solver_calls_frac                1.
% 1.71/0.99  --inst_passive_queue_type               priority_queues
% 1.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/0.99  --inst_passive_queues_freq              [25;2]
% 1.71/0.99  --inst_dismatching                      true
% 1.71/0.99  --inst_eager_unprocessed_to_passive     true
% 1.71/0.99  --inst_prop_sim_given                   true
% 1.71/0.99  --inst_prop_sim_new                     false
% 1.71/0.99  --inst_subs_new                         false
% 1.71/0.99  --inst_eq_res_simp                      false
% 1.71/0.99  --inst_subs_given                       false
% 1.71/0.99  --inst_orphan_elimination               true
% 1.71/0.99  --inst_learning_loop_flag               true
% 1.71/0.99  --inst_learning_start                   3000
% 1.71/0.99  --inst_learning_factor                  2
% 1.71/0.99  --inst_start_prop_sim_after_learn       3
% 1.71/0.99  --inst_sel_renew                        solver
% 1.71/0.99  --inst_lit_activity_flag                true
% 1.71/0.99  --inst_restr_to_given                   false
% 1.71/0.99  --inst_activity_threshold               500
% 1.71/0.99  --inst_out_proof                        true
% 1.71/0.99  
% 1.71/0.99  ------ Resolution Options
% 1.71/0.99  
% 1.71/0.99  --resolution_flag                       true
% 1.71/0.99  --res_lit_sel                           adaptive
% 1.71/0.99  --res_lit_sel_side                      none
% 1.71/0.99  --res_ordering                          kbo
% 1.71/0.99  --res_to_prop_solver                    active
% 1.71/0.99  --res_prop_simpl_new                    false
% 1.71/0.99  --res_prop_simpl_given                  true
% 1.71/0.99  --res_passive_queue_type                priority_queues
% 1.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/0.99  --res_passive_queues_freq               [15;5]
% 1.71/0.99  --res_forward_subs                      full
% 1.71/0.99  --res_backward_subs                     full
% 1.71/0.99  --res_forward_subs_resolution           true
% 1.71/0.99  --res_backward_subs_resolution          true
% 1.71/0.99  --res_orphan_elimination                true
% 1.71/0.99  --res_time_limit                        2.
% 1.71/0.99  --res_out_proof                         true
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Options
% 1.71/0.99  
% 1.71/0.99  --superposition_flag                    true
% 1.71/0.99  --sup_passive_queue_type                priority_queues
% 1.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.99  --demod_completeness_check              fast
% 1.71/0.99  --demod_use_ground                      true
% 1.71/0.99  --sup_to_prop_solver                    passive
% 1.71/0.99  --sup_prop_simpl_new                    true
% 1.71/0.99  --sup_prop_simpl_given                  true
% 1.71/0.99  --sup_fun_splitting                     false
% 1.71/0.99  --sup_smt_interval                      50000
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Simplification Setup
% 1.71/0.99  
% 1.71/0.99  --sup_indices_passive                   []
% 1.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_full_bw                           [BwDemod]
% 1.71/0.99  --sup_immed_triv                        [TrivRules]
% 1.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_immed_bw_main                     []
% 1.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  
% 1.71/0.99  ------ Combination Options
% 1.71/0.99  
% 1.71/0.99  --comb_res_mult                         3
% 1.71/0.99  --comb_sup_mult                         2
% 1.71/0.99  --comb_inst_mult                        10
% 1.71/0.99  
% 1.71/0.99  ------ Debug Options
% 1.71/0.99  
% 1.71/0.99  --dbg_backtrace                         false
% 1.71/0.99  --dbg_dump_prop_clauses                 false
% 1.71/0.99  --dbg_dump_prop_clauses_file            -
% 1.71/0.99  --dbg_out_stat                          false
% 1.71/0.99  ------ Parsing...
% 1.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 14 0s  sf_e  pe_s  pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.71/0.99  ------ Proving...
% 1.71/0.99  ------ Problem Properties 
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  clauses                                 6
% 1.71/0.99  conjectures                             0
% 1.71/0.99  EPR                                     0
% 1.71/0.99  Horn                                    5
% 1.71/0.99  unary                                   2
% 1.71/0.99  binary                                  2
% 1.71/0.99  lits                                    15
% 1.71/0.99  lits eq                                 15
% 1.71/0.99  fd_pure                                 0
% 1.71/0.99  fd_pseudo                               0
% 1.71/0.99  fd_cond                                 0
% 1.71/0.99  fd_pseudo_cond                          0
% 1.71/0.99  AC symbols                              0
% 1.71/0.99  
% 1.71/0.99  ------ Schedule dynamic 5 is on 
% 1.71/0.99  
% 1.71/0.99  ------ no conjectures: strip conj schedule 
% 1.71/0.99  
% 1.71/0.99  ------ pure equality problem: resolution off 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  ------ 
% 1.71/0.99  Current options:
% 1.71/0.99  ------ 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options
% 1.71/0.99  
% 1.71/0.99  --out_options                           all
% 1.71/0.99  --tptp_safe_out                         true
% 1.71/0.99  --problem_path                          ""
% 1.71/0.99  --include_path                          ""
% 1.71/0.99  --clausifier                            res/vclausify_rel
% 1.71/0.99  --clausifier_options                    --mode clausify
% 1.71/0.99  --stdin                                 false
% 1.71/0.99  --stats_out                             all
% 1.71/0.99  
% 1.71/0.99  ------ General Options
% 1.71/0.99  
% 1.71/0.99  --fof                                   false
% 1.71/0.99  --time_out_real                         305.
% 1.71/0.99  --time_out_virtual                      -1.
% 1.71/0.99  --symbol_type_check                     false
% 1.71/0.99  --clausify_out                          false
% 1.71/0.99  --sig_cnt_out                           false
% 1.71/0.99  --trig_cnt_out                          false
% 1.71/0.99  --trig_cnt_out_tolerance                1.
% 1.71/0.99  --trig_cnt_out_sk_spl                   false
% 1.71/0.99  --abstr_cl_out                          false
% 1.71/0.99  
% 1.71/0.99  ------ Global Options
% 1.71/0.99  
% 1.71/0.99  --schedule                              default
% 1.71/0.99  --add_important_lit                     false
% 1.71/0.99  --prop_solver_per_cl                    1000
% 1.71/0.99  --min_unsat_core                        false
% 1.71/0.99  --soft_assumptions                      false
% 1.71/0.99  --soft_lemma_size                       3
% 1.71/0.99  --prop_impl_unit_size                   0
% 1.71/0.99  --prop_impl_unit                        []
% 1.71/0.99  --share_sel_clauses                     true
% 1.71/0.99  --reset_solvers                         false
% 1.71/0.99  --bc_imp_inh                            [conj_cone]
% 1.71/0.99  --conj_cone_tolerance                   3.
% 1.71/0.99  --extra_neg_conj                        none
% 1.71/0.99  --large_theory_mode                     true
% 1.71/0.99  --prolific_symb_bound                   200
% 1.71/0.99  --lt_threshold                          2000
% 1.71/0.99  --clause_weak_htbl                      true
% 1.71/0.99  --gc_record_bc_elim                     false
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing Options
% 1.71/0.99  
% 1.71/0.99  --preprocessing_flag                    true
% 1.71/0.99  --time_out_prep_mult                    0.1
% 1.71/0.99  --splitting_mode                        input
% 1.71/0.99  --splitting_grd                         true
% 1.71/0.99  --splitting_cvd                         false
% 1.71/0.99  --splitting_cvd_svl                     false
% 1.71/0.99  --splitting_nvd                         32
% 1.71/0.99  --sub_typing                            true
% 1.71/0.99  --prep_gs_sim                           true
% 1.71/0.99  --prep_unflatten                        true
% 1.71/0.99  --prep_res_sim                          true
% 1.71/0.99  --prep_upred                            true
% 1.71/0.99  --prep_sem_filter                       exhaustive
% 1.71/0.99  --prep_sem_filter_out                   false
% 1.71/0.99  --pred_elim                             true
% 1.71/0.99  --res_sim_input                         true
% 1.71/0.99  --eq_ax_congr_red                       true
% 1.71/0.99  --pure_diseq_elim                       true
% 1.71/0.99  --brand_transform                       false
% 1.71/0.99  --non_eq_to_eq                          false
% 1.71/0.99  --prep_def_merge                        true
% 1.71/0.99  --prep_def_merge_prop_impl              false
% 1.71/0.99  --prep_def_merge_mbd                    true
% 1.71/0.99  --prep_def_merge_tr_red                 false
% 1.71/0.99  --prep_def_merge_tr_cl                  false
% 1.71/0.99  --smt_preprocessing                     true
% 1.71/0.99  --smt_ac_axioms                         fast
% 1.71/0.99  --preprocessed_out                      false
% 1.71/0.99  --preprocessed_stats                    false
% 1.71/0.99  
% 1.71/0.99  ------ Abstraction refinement Options
% 1.71/0.99  
% 1.71/0.99  --abstr_ref                             []
% 1.71/0.99  --abstr_ref_prep                        false
% 1.71/0.99  --abstr_ref_until_sat                   false
% 1.71/0.99  --abstr_ref_sig_restrict                funpre
% 1.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.99  --abstr_ref_under                       []
% 1.71/0.99  
% 1.71/0.99  ------ SAT Options
% 1.71/0.99  
% 1.71/0.99  --sat_mode                              false
% 1.71/0.99  --sat_fm_restart_options                ""
% 1.71/0.99  --sat_gr_def                            false
% 1.71/0.99  --sat_epr_types                         true
% 1.71/0.99  --sat_non_cyclic_types                  false
% 1.71/0.99  --sat_finite_models                     false
% 1.71/0.99  --sat_fm_lemmas                         false
% 1.71/0.99  --sat_fm_prep                           false
% 1.71/0.99  --sat_fm_uc_incr                        true
% 1.71/0.99  --sat_out_model                         small
% 1.71/0.99  --sat_out_clauses                       false
% 1.71/0.99  
% 1.71/0.99  ------ QBF Options
% 1.71/0.99  
% 1.71/0.99  --qbf_mode                              false
% 1.71/0.99  --qbf_elim_univ                         false
% 1.71/0.99  --qbf_dom_inst                          none
% 1.71/0.99  --qbf_dom_pre_inst                      false
% 1.71/0.99  --qbf_sk_in                             false
% 1.71/0.99  --qbf_pred_elim                         true
% 1.71/0.99  --qbf_split                             512
% 1.71/0.99  
% 1.71/0.99  ------ BMC1 Options
% 1.71/0.99  
% 1.71/0.99  --bmc1_incremental                      false
% 1.71/0.99  --bmc1_axioms                           reachable_all
% 1.71/0.99  --bmc1_min_bound                        0
% 1.71/0.99  --bmc1_max_bound                        -1
% 1.71/0.99  --bmc1_max_bound_default                -1
% 1.71/0.99  --bmc1_symbol_reachability              true
% 1.71/0.99  --bmc1_property_lemmas                  false
% 1.71/0.99  --bmc1_k_induction                      false
% 1.71/0.99  --bmc1_non_equiv_states                 false
% 1.71/0.99  --bmc1_deadlock                         false
% 1.71/0.99  --bmc1_ucm                              false
% 1.71/0.99  --bmc1_add_unsat_core                   none
% 1.71/0.99  --bmc1_unsat_core_children              false
% 1.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.99  --bmc1_out_stat                         full
% 1.71/0.99  --bmc1_ground_init                      false
% 1.71/0.99  --bmc1_pre_inst_next_state              false
% 1.71/0.99  --bmc1_pre_inst_state                   false
% 1.71/0.99  --bmc1_pre_inst_reach_state             false
% 1.71/0.99  --bmc1_out_unsat_core                   false
% 1.71/0.99  --bmc1_aig_witness_out                  false
% 1.71/0.99  --bmc1_verbose                          false
% 1.71/0.99  --bmc1_dump_clauses_tptp                false
% 1.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.99  --bmc1_dump_file                        -
% 1.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.99  --bmc1_ucm_extend_mode                  1
% 1.71/0.99  --bmc1_ucm_init_mode                    2
% 1.71/0.99  --bmc1_ucm_cone_mode                    none
% 1.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.99  --bmc1_ucm_relax_model                  4
% 1.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.99  --bmc1_ucm_layered_model                none
% 1.71/0.99  --bmc1_ucm_max_lemma_size               10
% 1.71/0.99  
% 1.71/0.99  ------ AIG Options
% 1.71/0.99  
% 1.71/0.99  --aig_mode                              false
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation Options
% 1.71/0.99  
% 1.71/0.99  --instantiation_flag                    true
% 1.71/0.99  --inst_sos_flag                         false
% 1.71/0.99  --inst_sos_phase                        true
% 1.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel_side                     none
% 1.71/0.99  --inst_solver_per_active                1400
% 1.71/0.99  --inst_solver_calls_frac                1.
% 1.71/0.99  --inst_passive_queue_type               priority_queues
% 1.71/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.71/0.99  --inst_passive_queues_freq              [25;2]
% 1.71/0.99  --inst_dismatching                      true
% 1.71/0.99  --inst_eager_unprocessed_to_passive     true
% 1.71/0.99  --inst_prop_sim_given                   true
% 1.71/0.99  --inst_prop_sim_new                     false
% 1.71/0.99  --inst_subs_new                         false
% 1.71/0.99  --inst_eq_res_simp                      false
% 1.71/0.99  --inst_subs_given                       false
% 1.71/0.99  --inst_orphan_elimination               true
% 1.71/0.99  --inst_learning_loop_flag               true
% 1.71/0.99  --inst_learning_start                   3000
% 1.71/0.99  --inst_learning_factor                  2
% 1.71/0.99  --inst_start_prop_sim_after_learn       3
% 1.71/0.99  --inst_sel_renew                        solver
% 1.71/0.99  --inst_lit_activity_flag                true
% 1.71/0.99  --inst_restr_to_given                   false
% 1.71/0.99  --inst_activity_threshold               500
% 1.71/0.99  --inst_out_proof                        true
% 1.71/0.99  
% 1.71/0.99  ------ Resolution Options
% 1.71/0.99  
% 1.71/0.99  --resolution_flag                       false
% 1.71/0.99  --res_lit_sel                           adaptive
% 1.71/0.99  --res_lit_sel_side                      none
% 1.71/0.99  --res_ordering                          kbo
% 1.71/0.99  --res_to_prop_solver                    active
% 1.71/0.99  --res_prop_simpl_new                    false
% 1.71/0.99  --res_prop_simpl_given                  true
% 1.71/0.99  --res_passive_queue_type                priority_queues
% 1.71/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.71/0.99  --res_passive_queues_freq               [15;5]
% 1.71/0.99  --res_forward_subs                      full
% 1.71/0.99  --res_backward_subs                     full
% 1.71/0.99  --res_forward_subs_resolution           true
% 1.71/0.99  --res_backward_subs_resolution          true
% 1.71/0.99  --res_orphan_elimination                true
% 1.71/0.99  --res_time_limit                        2.
% 1.71/0.99  --res_out_proof                         true
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Options
% 1.71/0.99  
% 1.71/0.99  --superposition_flag                    true
% 1.71/0.99  --sup_passive_queue_type                priority_queues
% 1.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.99  --demod_completeness_check              fast
% 1.71/0.99  --demod_use_ground                      true
% 1.71/0.99  --sup_to_prop_solver                    passive
% 1.71/0.99  --sup_prop_simpl_new                    true
% 1.71/0.99  --sup_prop_simpl_given                  true
% 1.71/0.99  --sup_fun_splitting                     false
% 1.71/0.99  --sup_smt_interval                      50000
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Simplification Setup
% 1.71/0.99  
% 1.71/0.99  --sup_indices_passive                   []
% 1.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_full_bw                           [BwDemod]
% 1.71/0.99  --sup_immed_triv                        [TrivRules]
% 1.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_immed_bw_main                     []
% 1.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  
% 1.71/0.99  ------ Combination Options
% 1.71/0.99  
% 1.71/0.99  --comb_res_mult                         3
% 1.71/0.99  --comb_sup_mult                         2
% 1.71/0.99  --comb_inst_mult                        10
% 1.71/0.99  
% 1.71/0.99  ------ Debug Options
% 1.71/0.99  
% 1.71/0.99  --dbg_backtrace                         false
% 1.71/0.99  --dbg_dump_prop_clauses                 false
% 1.71/0.99  --dbg_dump_prop_clauses_file            -
% 1.71/0.99  --dbg_out_stat                          false
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  ------ Proving...
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  % SZS output start Saturation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  fof(f7,axiom,(
% 1.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f26,plain,(
% 1.71/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.99    inference(ennf_transformation,[],[f7])).
% 1.71/0.99  
% 1.71/0.99  fof(f53,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.99    inference(cnf_transformation,[],[f26])).
% 1.71/0.99  
% 1.71/0.99  fof(f13,conjecture,(
% 1.71/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f14,negated_conjecture,(
% 1.71/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 1.71/0.99    inference(negated_conjecture,[],[f13])).
% 1.71/0.99  
% 1.71/0.99  fof(f15,plain,(
% 1.71/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 1.71/0.99    inference(pure_predicate_removal,[],[f14])).
% 1.71/0.99  
% 1.71/0.99  fof(f35,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f15])).
% 1.71/0.99  
% 1.71/0.99  fof(f36,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 1.71/0.99    inference(flattening,[],[f35])).
% 1.71/0.99  
% 1.71/0.99  fof(f40,plain,(
% 1.71/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f39,plain,(
% 1.71/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1))) )),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f38,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f41,plain,(
% 1.71/0.99    (((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39,f38])).
% 1.71/0.99  
% 1.71/0.99  fof(f72,plain,(
% 1.71/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f10,axiom,(
% 1.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f30,plain,(
% 1.71/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.99    inference(ennf_transformation,[],[f10])).
% 1.71/0.99  
% 1.71/0.99  fof(f31,plain,(
% 1.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.99    inference(flattening,[],[f30])).
% 1.71/0.99  
% 1.71/0.99  fof(f61,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f31])).
% 1.71/0.99  
% 1.71/0.99  fof(f2,axiom,(
% 1.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f16,plain,(
% 1.71/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f2])).
% 1.71/0.99  
% 1.71/0.99  fof(f17,plain,(
% 1.71/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f16])).
% 1.71/0.99  
% 1.71/0.99  fof(f44,plain,(
% 1.71/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f17])).
% 1.71/0.99  
% 1.71/0.99  fof(f70,plain,(
% 1.71/0.99    v1_funct_1(sK2)),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f62,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f31])).
% 1.71/0.99  
% 1.71/0.99  fof(f63,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f31])).
% 1.71/0.99  
% 1.71/0.99  fof(f6,axiom,(
% 1.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f24,plain,(
% 1.71/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f6])).
% 1.71/0.99  
% 1.71/0.99  fof(f25,plain,(
% 1.71/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f24])).
% 1.71/0.99  
% 1.71/0.99  fof(f52,plain,(
% 1.71/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f25])).
% 1.71/0.99  
% 1.71/0.99  fof(f5,axiom,(
% 1.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f22,plain,(
% 1.71/0.99    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f5])).
% 1.71/0.99  
% 1.71/0.99  fof(f23,plain,(
% 1.71/0.99    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f22])).
% 1.71/0.99  
% 1.71/0.99  fof(f50,plain,(
% 1.71/0.99    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f23])).
% 1.71/0.99  
% 1.71/0.99  fof(f51,plain,(
% 1.71/0.99    ( ! [X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f23])).
% 1.71/0.99  
% 1.71/0.99  fof(f4,axiom,(
% 1.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f20,plain,(
% 1.71/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f4])).
% 1.71/0.99  
% 1.71/0.99  fof(f21,plain,(
% 1.71/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f20])).
% 1.71/0.99  
% 1.71/0.99  fof(f48,plain,(
% 1.71/0.99    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f21])).
% 1.71/0.99  
% 1.71/0.99  fof(f49,plain,(
% 1.71/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f21])).
% 1.71/0.99  
% 1.71/0.99  fof(f3,axiom,(
% 1.71/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f18,plain,(
% 1.71/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f3])).
% 1.71/0.99  
% 1.71/0.99  fof(f19,plain,(
% 1.71/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.99    inference(flattening,[],[f18])).
% 1.71/0.99  
% 1.71/0.99  fof(f47,plain,(
% 1.71/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f19])).
% 1.71/0.99  
% 1.71/0.99  fof(f43,plain,(
% 1.71/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f17])).
% 1.71/0.99  
% 1.71/0.99  fof(f8,axiom,(
% 1.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f27,plain,(
% 1.71/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.99    inference(ennf_transformation,[],[f8])).
% 1.71/0.99  
% 1.71/0.99  fof(f54,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.99    inference(cnf_transformation,[],[f27])).
% 1.71/0.99  
% 1.71/0.99  fof(f71,plain,(
% 1.71/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f9,axiom,(
% 1.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f28,plain,(
% 1.71/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.99    inference(ennf_transformation,[],[f9])).
% 1.71/0.99  
% 1.71/0.99  fof(f29,plain,(
% 1.71/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.99    inference(flattening,[],[f28])).
% 1.71/0.99  
% 1.71/0.99  fof(f37,plain,(
% 1.71/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.99    inference(nnf_transformation,[],[f29])).
% 1.71/0.99  
% 1.71/0.99  fof(f55,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.99    inference(cnf_transformation,[],[f37])).
% 1.71/0.99  
% 1.71/0.99  fof(f1,axiom,(
% 1.71/0.99    v1_xboole_0(k1_xboole_0)),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f42,plain,(
% 1.71/0.99    v1_xboole_0(k1_xboole_0)),
% 1.71/0.99    inference(cnf_transformation,[],[f1])).
% 1.71/0.99  
% 1.71/0.99  fof(f11,axiom,(
% 1.71/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f32,plain,(
% 1.71/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f11])).
% 1.71/0.99  
% 1.71/0.99  fof(f33,plain,(
% 1.71/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.71/0.99    inference(flattening,[],[f32])).
% 1.71/0.99  
% 1.71/0.99  fof(f64,plain,(
% 1.71/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f33])).
% 1.71/0.99  
% 1.71/0.99  fof(f12,axiom,(
% 1.71/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f34,plain,(
% 1.71/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f12])).
% 1.71/0.99  
% 1.71/0.99  fof(f65,plain,(
% 1.71/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f69,plain,(
% 1.71/0.99    l1_orders_2(sK1)),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f68,plain,(
% 1.71/0.99    ~v2_struct_0(sK1)),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f73,plain,(
% 1.71/0.99    k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f67,plain,(
% 1.71/0.99    l1_orders_2(sK0)),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f66,plain,(
% 1.71/0.99    ~v2_struct_0(sK0)),
% 1.71/0.99    inference(cnf_transformation,[],[f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f57,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.99    inference(cnf_transformation,[],[f37])).
% 1.71/0.99  
% 1.71/0.99  cnf(c_11,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_25,negated_conjecture,
% 1.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.71/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_471,plain,
% 1.71/0.99      ( v1_relat_1(X0)
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.71/0.99      | sK2 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_472,plain,
% 1.71/0.99      ( v1_relat_1(sK2)
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_471]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_21,plain,
% 1.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/0.99      | ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | v1_funct_1(k2_funct_1(X0))
% 1.71/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.71/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1,plain,
% 1.71/0.99      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 1.71/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_185,plain,
% 1.71/0.99      ( v1_funct_1(k2_funct_1(X0))
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_21,c_11,c_1]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_186,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_185]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_408,plain,
% 1.71/0.99      ( ~ v1_funct_1(X0)
% 1.71/0.99      | v1_funct_1(k2_funct_1(X0))
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.71/0.99      | sK2 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_186,c_25]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_409,plain,
% 1.71/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 1.71/0.99      | ~ v1_funct_1(sK2)
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_27,negated_conjecture,
% 1.71/0.99      ( v1_funct_1(sK2) ),
% 1.71/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_413,plain,
% 1.71/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_409,c_27]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_331,plain,
% 1.71/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_330,plain,
% 1.71/0.99      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_328,plain,
% 1.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.71/0.99      | v1_funct_2(X3,X4,X5)
% 1.71/0.99      | X3 != X0
% 1.71/0.99      | X4 != X1
% 1.71/0.99      | X5 != X2 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_326,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_320,plain,
% 1.71/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_319,plain,
% 1.71/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_318,plain,
% 1.71/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_316,plain,
% 1.71/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_313,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_20,plain,
% 1.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.71/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/0.99      | ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.71/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_19,plain,
% 1.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.71/0.99      | ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.71/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_10,plain,
% 1.71/0.99      ( ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_9,plain,
% 1.71/0.99      ( ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_8,plain,
% 1.71/0.99      ( ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_7,plain,
% 1.71/0.99      ( ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_6,plain,
% 1.71/0.99      ( ~ v2_funct_1(X0)
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0)
% 1.71/0.99      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_3,plain,
% 1.71/0.99      ( ~ v2_funct_1(X0)
% 1.71/0.99      | v2_funct_1(k2_funct_1(X0))
% 1.71/0.99      | ~ v1_relat_1(X0)
% 1.71/0.99      | ~ v1_funct_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2,plain,
% 1.71/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_12,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_462,plain,
% 1.71/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.71/0.99      | sK2 != X2 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_463,plain,
% 1.71/0.99      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_462]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_730,plain,
% 1.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.71/0.99      | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_463]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_791,plain,
% 1.71/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 1.71/0.99      inference(equality_resolution,[status(thm)],[c_730]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_26,negated_conjecture,
% 1.71/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.71/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_18,plain,
% 1.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.71/0.99      | k1_xboole_0 = X2 ),
% 1.71/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_426,plain,
% 1.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.71/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.71/0.99      | sK2 != X0
% 1.71/0.99      | k1_xboole_0 = X2 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_427,plain,
% 1.71/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 1.71/0.99      | k1_relset_1(X0,X1,sK2) = X0
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.71/0.99      | k1_xboole_0 = X1 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_426]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_648,plain,
% 1.71/0.99      ( k1_relset_1(X0,X1,sK2) = X0
% 1.71/0.99      | u1_struct_0(sK1) != X1
% 1.71/0.99      | u1_struct_0(sK0) != X0
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.71/0.99      | sK2 != sK2
% 1.71/0.99      | k1_xboole_0 = X1 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_427]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_649,plain,
% 1.71/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 1.71/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_648]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_727,plain,
% 1.71/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 1.71/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_649]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_833,plain,
% 1.71/0.99      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_791,c_727]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_0,plain,
% 1.71/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_22,plain,
% 1.71/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.71/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_354,plain,
% 1.71/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_22]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_23,plain,
% 1.71/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_28,negated_conjecture,
% 1.71/0.99      ( l1_orders_2(sK1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_372,plain,
% 1.71/0.99      ( l1_struct_0(X0) | sK1 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_373,plain,
% 1.71/0.99      ( l1_struct_0(sK1) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_372]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_390,plain,
% 1.71/0.99      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_354,c_373]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_391,plain,
% 1.71/0.99      ( v2_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_29,negated_conjecture,
% 1.71/0.99      ( ~ v2_struct_0(sK1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_393,plain,
% 1.71/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 1.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_391,c_29]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_732,plain,
% 1.71/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_393]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_867,plain,
% 1.71/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_833,c_732]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_874,plain,
% 1.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.71/0.99      | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_867,c_730]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_24,negated_conjecture,
% 1.71/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.71/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_548,plain,
% 1.71/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.71/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.71/0.99      | k2_funct_1(sK2) != sK2 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_25]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_555,plain,
% 1.71/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.71/0.99      | k2_funct_1(sK2) != sK2 ),
% 1.71/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_548,c_413]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_616,plain,
% 1.71/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.71/0.99      | k2_funct_1(sK2) != sK2 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_555,c_26]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_729,plain,
% 1.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_616]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_873,plain,
% 1.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | u1_struct_0(sK1) != k1_relat_1(sK2)
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_867,c_729]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_30,negated_conjecture,
% 1.71/0.99      ( l1_orders_2(sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_379,plain,
% 1.71/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_380,plain,
% 1.71/0.99      ( l1_struct_0(sK0) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_379]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_398,plain,
% 1.71/0.99      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK0 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_354,c_380]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_399,plain,
% 1.71/0.99      ( v2_struct_0(sK0) | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_398]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_31,negated_conjecture,
% 1.71/0.99      ( ~ v2_struct_0(sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_401,plain,
% 1.71/0.99      ( u1_struct_0(sK0) != k1_xboole_0 ),
% 1.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_399,c_31]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_731,plain,
% 1.71/0.99      ( u1_struct_0(sK0) != k1_xboole_0 ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_401]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_872,plain,
% 1.71/0.99      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_867,c_731]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_871,plain,
% 1.71/0.99      ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_867,c_791]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_16,plain,
% 1.71/0.99      ( v1_funct_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/0.99      | k1_relset_1(X1,X2,X0) != X1
% 1.71/0.99      | k1_xboole_0 = X2 ),
% 1.71/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_444,plain,
% 1.71/0.99      ( v1_funct_2(X0,X1,X2)
% 1.71/0.99      | k1_relset_1(X1,X2,X0) != X1
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.71/0.99      | sK2 != X0
% 1.71/0.99      | k1_xboole_0 = X2 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_445,plain,
% 1.71/0.99      ( v1_funct_2(sK2,X0,X1)
% 1.71/0.99      | k1_relset_1(X0,X1,sK2) != X0
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.71/0.99      | k1_xboole_0 = X1 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_629,plain,
% 1.71/0.99      ( k1_relset_1(X0,X1,sK2) != X0
% 1.71/0.99      | u1_struct_0(sK1) != X0
% 1.71/0.99      | u1_struct_0(sK0) != X1
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | k1_xboole_0 = X1 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_555,c_445]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_630,plain,
% 1.71/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | k1_xboole_0 = u1_struct_0(sK0) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_728,plain,
% 1.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.71/0.99      | k1_xboole_0 = u1_struct_0(sK0) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_630]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_737,plain,
% 1.71/0.99      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_798,plain,
% 1.71/0.99      ( u1_struct_0(sK0) != X0_50
% 1.71/0.99      | u1_struct_0(sK0) = k1_xboole_0
% 1.71/0.99      | k1_xboole_0 != X0_50 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_737]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_807,plain,
% 1.71/0.99      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.71/0.99      | u1_struct_0(sK0) = k1_xboole_0
% 1.71/0.99      | k1_xboole_0 != u1_struct_0(sK0) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_798]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_733,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_808,plain,
% 1.71/0.99      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_733]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_861,plain,
% 1.71/0.99      ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.71/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_728,c_731,c_807,c_808]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_862,plain,
% 1.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_861]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_870,plain,
% 1.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
% 1.71/0.99      | k2_funct_1(sK2) != sK2
% 1.71/0.99      | k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),sK2) != u1_struct_0(sK1)
% 1.71/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 1.71/0.99      inference(demodulation,[status(thm)],[c_867,c_862]) ).
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS output end Saturation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  ------                               Statistics
% 1.71/0.99  
% 1.71/0.99  ------ General
% 1.71/0.99  
% 1.71/0.99  abstr_ref_over_cycles:                  0
% 1.71/0.99  abstr_ref_under_cycles:                 0
% 1.71/0.99  gc_basic_clause_elim:                   0
% 1.71/0.99  forced_gc_time:                         0
% 1.71/0.99  parsing_time:                           0.011
% 1.71/0.99  unif_index_cands_time:                  0.
% 1.71/0.99  unif_index_add_time:                    0.
% 1.71/0.99  orderings_time:                         0.
% 1.71/0.99  out_proof_time:                         0.
% 1.71/0.99  total_time:                             0.074
% 1.71/0.99  num_of_symbols:                         58
% 1.71/0.99  num_of_terms:                           1102
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing
% 1.71/0.99  
% 1.71/0.99  num_of_splits:                          0
% 1.71/0.99  num_of_split_atoms:                     0
% 1.71/0.99  num_of_reused_defs:                     0
% 1.71/0.99  num_eq_ax_congr_red:                    7
% 1.71/0.99  num_of_sem_filtered_clauses:            13
% 1.71/0.99  num_of_subtypes:                        5
% 1.71/0.99  monotx_restored_types:                  0
% 1.71/0.99  sat_num_of_epr_types:                   0
% 1.71/0.99  sat_num_of_non_cyclic_types:            0
% 1.71/0.99  sat_guarded_non_collapsed_types:        0
% 1.71/0.99  num_pure_diseq_elim:                    0
% 1.71/0.99  simp_replaced_by:                       0
% 1.71/0.99  res_preprocessed:                       66
% 1.71/0.99  prep_upred:                             0
% 1.71/0.99  prep_unflattend:                        33
% 1.71/0.99  smt_new_axioms:                         0
% 1.71/0.99  pred_elim_cands:                        0
% 1.71/0.99  pred_elim:                              6
% 1.71/0.99  pred_elim_cl:                           11
% 1.71/0.99  pred_elim_cycles:                       7
% 1.71/0.99  merged_defs:                            0
% 1.71/0.99  merged_defs_ncl:                        0
% 1.71/0.99  bin_hyper_res:                          0
% 1.71/0.99  prep_cycles:                            4
% 1.71/0.99  pred_elim_time:                         0.007
% 1.71/0.99  splitting_time:                         0.
% 1.71/0.99  sem_filter_time:                        0.
% 1.71/0.99  monotx_time:                            0.
% 1.71/0.99  subtype_inf_time:                       0.
% 1.71/0.99  
% 1.71/0.99  ------ Problem properties
% 1.71/0.99  
% 1.71/0.99  clauses:                                6
% 1.71/0.99  conjectures:                            0
% 1.71/0.99  epr:                                    0
% 1.71/0.99  horn:                                   5
% 1.71/0.99  ground:                                 5
% 1.71/0.99  unary:                                  2
% 1.71/0.99  binary:                                 2
% 1.71/0.99  lits:                                   15
% 1.71/0.99  lits_eq:                                15
% 1.71/0.99  fd_pure:                                0
% 1.71/0.99  fd_pseudo:                              0
% 1.71/0.99  fd_cond:                                0
% 1.71/0.99  fd_pseudo_cond:                         0
% 1.71/0.99  ac_symbols:                             0
% 1.71/0.99  
% 1.71/0.99  ------ Propositional Solver
% 1.71/0.99  
% 1.71/0.99  prop_solver_calls:                      26
% 1.71/0.99  prop_fast_solver_calls:                 455
% 1.71/0.99  smt_solver_calls:                       0
% 1.71/0.99  smt_fast_solver_calls:                  0
% 1.71/0.99  prop_num_of_clauses:                    286
% 1.71/0.99  prop_preprocess_simplified:             1528
% 1.71/0.99  prop_fo_subsumed:                       10
% 1.71/0.99  prop_solver_time:                       0.
% 1.71/0.99  smt_solver_time:                        0.
% 1.71/0.99  smt_fast_solver_time:                   0.
% 1.71/0.99  prop_fast_solver_time:                  0.
% 1.71/0.99  prop_unsat_core_time:                   0.
% 1.71/0.99  
% 1.71/0.99  ------ QBF
% 1.71/0.99  
% 1.71/0.99  qbf_q_res:                              0
% 1.71/0.99  qbf_num_tautologies:                    0
% 1.71/0.99  qbf_prep_cycles:                        0
% 1.71/0.99  
% 1.71/0.99  ------ BMC1
% 1.71/0.99  
% 1.71/0.99  bmc1_current_bound:                     -1
% 1.71/0.99  bmc1_last_solved_bound:                 -1
% 1.71/0.99  bmc1_unsat_core_size:                   -1
% 1.71/0.99  bmc1_unsat_core_parents_size:           -1
% 1.71/0.99  bmc1_merge_next_fun:                    0
% 1.71/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation
% 1.71/0.99  
% 1.71/0.99  inst_num_of_clauses:                    79
% 1.71/0.99  inst_num_in_passive:                    1
% 1.71/0.99  inst_num_in_active:                     66
% 1.71/0.99  inst_num_in_unprocessed:                12
% 1.71/0.99  inst_num_of_loops:                      70
% 1.71/0.99  inst_num_of_learning_restarts:          0
% 1.71/0.99  inst_num_moves_active_passive:          1
% 1.71/0.99  inst_lit_activity:                      0
% 1.71/0.99  inst_lit_activity_moves:                0
% 1.71/0.99  inst_num_tautologies:                   0
% 1.71/0.99  inst_num_prop_implied:                  0
% 1.71/0.99  inst_num_existing_simplified:           0
% 1.71/0.99  inst_num_eq_res_simplified:             0
% 1.71/0.99  inst_num_child_elim:                    0
% 1.71/0.99  inst_num_of_dismatching_blockings:      7
% 1.71/0.99  inst_num_of_non_proper_insts:           79
% 1.71/0.99  inst_num_of_duplicates:                 0
% 1.71/0.99  inst_inst_num_from_inst_to_res:         0
% 1.71/0.99  inst_dismatching_checking_time:         0.
% 1.71/0.99  
% 1.71/0.99  ------ Resolution
% 1.71/0.99  
% 1.71/0.99  res_num_of_clauses:                     0
% 1.71/0.99  res_num_in_passive:                     0
% 1.71/0.99  res_num_in_active:                      0
% 1.71/0.99  res_num_of_loops:                       70
% 1.71/0.99  res_forward_subset_subsumed:            29
% 1.71/0.99  res_backward_subset_subsumed:           0
% 1.71/0.99  res_forward_subsumed:                   0
% 1.71/0.99  res_backward_subsumed:                  0
% 1.71/0.99  res_forward_subsumption_resolution:     1
% 1.71/0.99  res_backward_subsumption_resolution:    0
% 1.71/0.99  res_clause_to_clause_subsumption:       21
% 1.71/0.99  res_orphan_elimination:                 0
% 1.71/0.99  res_tautology_del:                      27
% 1.71/0.99  res_num_eq_res_simplified:              0
% 1.71/0.99  res_num_sel_changes:                    0
% 1.71/0.99  res_moves_from_active_to_pass:          0
% 1.71/0.99  
% 1.71/0.99  ------ Superposition
% 1.71/0.99  
% 1.71/0.99  sup_time_total:                         0.
% 1.71/0.99  sup_time_generating:                    0.
% 1.71/0.99  sup_time_sim_full:                      0.
% 1.71/0.99  sup_time_sim_immed:                     0.
% 1.71/0.99  
% 1.71/0.99  sup_num_of_clauses:                     7
% 1.71/0.99  sup_num_in_active:                      7
% 1.71/0.99  sup_num_in_passive:                     0
% 1.71/0.99  sup_num_of_loops:                       13
% 1.71/0.99  sup_fw_superposition:                   0
% 1.71/0.99  sup_bw_superposition:                   0
% 1.71/0.99  sup_immediate_simplified:               0
% 1.71/0.99  sup_given_eliminated:                   0
% 1.71/0.99  comparisons_done:                       0
% 1.71/0.99  comparisons_avoided:                    0
% 1.71/0.99  
% 1.71/0.99  ------ Simplifications
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  sim_fw_subset_subsumed:                 0
% 1.71/0.99  sim_bw_subset_subsumed:                 0
% 1.71/0.99  sim_fw_subsumed:                        0
% 1.71/0.99  sim_bw_subsumed:                        0
% 1.71/0.99  sim_fw_subsumption_res:                 0
% 1.71/0.99  sim_bw_subsumption_res:                 0
% 1.71/0.99  sim_tautology_del:                      0
% 1.71/0.99  sim_eq_tautology_del:                   0
% 1.71/0.99  sim_eq_res_simp:                        0
% 1.71/0.99  sim_fw_demodulated:                     0
% 1.71/0.99  sim_bw_demodulated:                     6
% 1.71/0.99  sim_light_normalised:                   0
% 1.71/0.99  sim_joinable_taut:                      0
% 1.71/0.99  sim_joinable_simp:                      0
% 1.71/0.99  sim_ac_normalised:                      0
% 1.71/0.99  sim_smt_subsumption:                    0
% 1.71/0.99  
%------------------------------------------------------------------------------
