%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:18 EST 2020

% Result     : CounterSatisfiable 0.73s
% Output     : Saturation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 190 expanded)
%              Number of clauses        :   45 (  54 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  328 (1162 expanded)
%              Number of equality atoms :   96 ( 205 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ~ v2_struct_0(X0)
       => ! [X1] :
            ( ~ v2_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
       => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
          & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_funct_1(X2)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
        | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
        | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
          | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2) )
   => ( ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_144,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_139,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_136,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_284,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_283,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_422,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_178,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_179,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_178])).

cnf(c_279,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_426,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_44)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_519,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_426])).

cnf(c_605,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_422,c_519])).

cnf(c_10,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_154,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_200,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_154,c_11])).

cnf(c_277,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(subtyping,[status(esa)],[c_200])).

cnf(c_427,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_295,plain,
    ( ~ v1_funct_1(X0_44)
    | v1_funct_1(X1_44)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_507,plain,
    ( ~ v1_funct_1(X0_44)
    | v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0_44 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_509,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_561,plain,
    ( k2_funct_1(sK2) != sK2
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_13,c_277,c_509])).

cnf(c_562,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(renaming,[status(thm)],[c_561])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_191,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_192,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_278,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))
    | k2_relset_1(X0_45,X1_45,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_192])).

cnf(c_499,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_278])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_281,plain,
    ( ~ v1_funct_1(X0_44)
    | ~ v1_relat_1(X0_44)
    | v1_relat_1(k2_funct_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_424,plain,
    ( v1_funct_1(X0_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k2_funct_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_282,plain,
    ( ~ v1_funct_1(X0_44)
    | v1_funct_1(k2_funct_1(X0_44))
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_423,plain,
    ( v1_funct_1(X0_44) != iProver_top
    | v1_funct_1(k2_funct_1(X0_44)) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_280,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_425,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.73/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.73/1.00  
% 0.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.73/1.00  
% 0.73/1.00  ------  iProver source info
% 0.73/1.00  
% 0.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.73/1.00  git: non_committed_changes: false
% 0.73/1.00  git: last_make_outside_of_git: false
% 0.73/1.00  
% 0.73/1.00  ------ 
% 0.73/1.00  
% 0.73/1.00  ------ Input Options
% 0.73/1.00  
% 0.73/1.00  --out_options                           all
% 0.73/1.00  --tptp_safe_out                         true
% 0.73/1.00  --problem_path                          ""
% 0.73/1.00  --include_path                          ""
% 0.73/1.00  --clausifier                            res/vclausify_rel
% 0.73/1.00  --clausifier_options                    --mode clausify
% 0.73/1.00  --stdin                                 false
% 0.73/1.00  --stats_out                             all
% 0.73/1.00  
% 0.73/1.00  ------ General Options
% 0.73/1.00  
% 0.73/1.00  --fof                                   false
% 0.73/1.00  --time_out_real                         305.
% 0.73/1.00  --time_out_virtual                      -1.
% 0.73/1.00  --symbol_type_check                     false
% 0.73/1.00  --clausify_out                          false
% 0.73/1.00  --sig_cnt_out                           false
% 0.73/1.00  --trig_cnt_out                          false
% 0.73/1.00  --trig_cnt_out_tolerance                1.
% 0.73/1.00  --trig_cnt_out_sk_spl                   false
% 0.73/1.00  --abstr_cl_out                          false
% 0.73/1.00  
% 0.73/1.00  ------ Global Options
% 0.73/1.00  
% 0.73/1.00  --schedule                              default
% 0.73/1.00  --add_important_lit                     false
% 0.73/1.00  --prop_solver_per_cl                    1000
% 0.73/1.00  --min_unsat_core                        false
% 0.73/1.00  --soft_assumptions                      false
% 0.73/1.00  --soft_lemma_size                       3
% 0.73/1.00  --prop_impl_unit_size                   0
% 0.73/1.00  --prop_impl_unit                        []
% 0.73/1.00  --share_sel_clauses                     true
% 0.73/1.00  --reset_solvers                         false
% 0.73/1.00  --bc_imp_inh                            [conj_cone]
% 0.73/1.00  --conj_cone_tolerance                   3.
% 0.73/1.00  --extra_neg_conj                        none
% 0.73/1.00  --large_theory_mode                     true
% 0.73/1.00  --prolific_symb_bound                   200
% 0.73/1.00  --lt_threshold                          2000
% 0.73/1.00  --clause_weak_htbl                      true
% 0.73/1.00  --gc_record_bc_elim                     false
% 0.73/1.00  
% 0.73/1.00  ------ Preprocessing Options
% 0.73/1.00  
% 0.73/1.00  --preprocessing_flag                    true
% 0.73/1.00  --time_out_prep_mult                    0.1
% 0.73/1.00  --splitting_mode                        input
% 0.73/1.00  --splitting_grd                         true
% 0.73/1.00  --splitting_cvd                         false
% 0.73/1.00  --splitting_cvd_svl                     false
% 0.73/1.00  --splitting_nvd                         32
% 0.73/1.00  --sub_typing                            true
% 0.73/1.00  --prep_gs_sim                           true
% 0.73/1.00  --prep_unflatten                        true
% 0.73/1.00  --prep_res_sim                          true
% 0.73/1.00  --prep_upred                            true
% 0.73/1.00  --prep_sem_filter                       exhaustive
% 0.73/1.00  --prep_sem_filter_out                   false
% 0.73/1.00  --pred_elim                             true
% 0.73/1.00  --res_sim_input                         true
% 0.73/1.00  --eq_ax_congr_red                       true
% 0.73/1.00  --pure_diseq_elim                       true
% 0.73/1.00  --brand_transform                       false
% 0.73/1.00  --non_eq_to_eq                          false
% 0.73/1.00  --prep_def_merge                        true
% 0.73/1.00  --prep_def_merge_prop_impl              false
% 0.73/1.00  --prep_def_merge_mbd                    true
% 0.73/1.00  --prep_def_merge_tr_red                 false
% 0.73/1.00  --prep_def_merge_tr_cl                  false
% 0.73/1.00  --smt_preprocessing                     true
% 0.73/1.00  --smt_ac_axioms                         fast
% 0.73/1.00  --preprocessed_out                      false
% 0.73/1.00  --preprocessed_stats                    false
% 0.73/1.00  
% 0.73/1.00  ------ Abstraction refinement Options
% 0.73/1.00  
% 0.73/1.00  --abstr_ref                             []
% 0.73/1.00  --abstr_ref_prep                        false
% 0.73/1.00  --abstr_ref_until_sat                   false
% 0.73/1.00  --abstr_ref_sig_restrict                funpre
% 0.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.00  --abstr_ref_under                       []
% 0.73/1.00  
% 0.73/1.00  ------ SAT Options
% 0.73/1.00  
% 0.73/1.00  --sat_mode                              false
% 0.73/1.00  --sat_fm_restart_options                ""
% 0.73/1.00  --sat_gr_def                            false
% 0.73/1.00  --sat_epr_types                         true
% 0.73/1.00  --sat_non_cyclic_types                  false
% 0.73/1.00  --sat_finite_models                     false
% 0.73/1.00  --sat_fm_lemmas                         false
% 0.73/1.00  --sat_fm_prep                           false
% 0.73/1.00  --sat_fm_uc_incr                        true
% 0.73/1.00  --sat_out_model                         small
% 0.73/1.00  --sat_out_clauses                       false
% 0.73/1.00  
% 0.73/1.00  ------ QBF Options
% 0.73/1.00  
% 0.73/1.00  --qbf_mode                              false
% 0.73/1.00  --qbf_elim_univ                         false
% 0.73/1.00  --qbf_dom_inst                          none
% 0.73/1.00  --qbf_dom_pre_inst                      false
% 0.73/1.00  --qbf_sk_in                             false
% 0.73/1.00  --qbf_pred_elim                         true
% 0.73/1.00  --qbf_split                             512
% 0.73/1.00  
% 0.73/1.00  ------ BMC1 Options
% 0.73/1.00  
% 0.73/1.00  --bmc1_incremental                      false
% 0.73/1.00  --bmc1_axioms                           reachable_all
% 0.73/1.00  --bmc1_min_bound                        0
% 0.73/1.00  --bmc1_max_bound                        -1
% 0.73/1.00  --bmc1_max_bound_default                -1
% 0.73/1.00  --bmc1_symbol_reachability              true
% 0.73/1.00  --bmc1_property_lemmas                  false
% 0.73/1.00  --bmc1_k_induction                      false
% 0.73/1.00  --bmc1_non_equiv_states                 false
% 0.73/1.00  --bmc1_deadlock                         false
% 0.73/1.00  --bmc1_ucm                              false
% 0.73/1.00  --bmc1_add_unsat_core                   none
% 0.73/1.00  --bmc1_unsat_core_children              false
% 0.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.00  --bmc1_out_stat                         full
% 0.73/1.00  --bmc1_ground_init                      false
% 0.73/1.00  --bmc1_pre_inst_next_state              false
% 0.73/1.00  --bmc1_pre_inst_state                   false
% 0.73/1.00  --bmc1_pre_inst_reach_state             false
% 0.73/1.00  --bmc1_out_unsat_core                   false
% 0.73/1.00  --bmc1_aig_witness_out                  false
% 0.73/1.00  --bmc1_verbose                          false
% 0.73/1.00  --bmc1_dump_clauses_tptp                false
% 0.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.00  --bmc1_dump_file                        -
% 0.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.00  --bmc1_ucm_extend_mode                  1
% 0.73/1.00  --bmc1_ucm_init_mode                    2
% 0.73/1.00  --bmc1_ucm_cone_mode                    none
% 0.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.00  --bmc1_ucm_relax_model                  4
% 0.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.00  --bmc1_ucm_layered_model                none
% 0.73/1.00  --bmc1_ucm_max_lemma_size               10
% 0.73/1.00  
% 0.73/1.00  ------ AIG Options
% 0.73/1.00  
% 0.73/1.00  --aig_mode                              false
% 0.73/1.00  
% 0.73/1.00  ------ Instantiation Options
% 0.73/1.00  
% 0.73/1.00  --instantiation_flag                    true
% 0.73/1.00  --inst_sos_flag                         false
% 0.73/1.00  --inst_sos_phase                        true
% 0.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.00  --inst_lit_sel_side                     num_symb
% 0.73/1.00  --inst_solver_per_active                1400
% 0.73/1.00  --inst_solver_calls_frac                1.
% 0.73/1.00  --inst_passive_queue_type               priority_queues
% 0.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.73/1.00  --inst_passive_queues_freq              [25;2]
% 0.73/1.00  --inst_dismatching                      true
% 0.73/1.00  --inst_eager_unprocessed_to_passive     true
% 0.73/1.00  --inst_prop_sim_given                   true
% 0.73/1.00  --inst_prop_sim_new                     false
% 0.73/1.00  --inst_subs_new                         false
% 0.73/1.00  --inst_eq_res_simp                      false
% 0.73/1.00  --inst_subs_given                       false
% 0.73/1.00  --inst_orphan_elimination               true
% 0.73/1.00  --inst_learning_loop_flag               true
% 0.73/1.00  --inst_learning_start                   3000
% 0.73/1.00  --inst_learning_factor                  2
% 0.73/1.00  --inst_start_prop_sim_after_learn       3
% 0.73/1.00  --inst_sel_renew                        solver
% 0.73/1.00  --inst_lit_activity_flag                true
% 0.73/1.00  --inst_restr_to_given                   false
% 0.73/1.00  --inst_activity_threshold               500
% 0.73/1.00  --inst_out_proof                        true
% 0.73/1.00  
% 0.73/1.00  ------ Resolution Options
% 0.73/1.00  
% 0.73/1.00  --resolution_flag                       true
% 0.73/1.00  --res_lit_sel                           adaptive
% 0.73/1.00  --res_lit_sel_side                      none
% 0.73/1.00  --res_ordering                          kbo
% 0.73/1.00  --res_to_prop_solver                    active
% 0.73/1.00  --res_prop_simpl_new                    false
% 0.73/1.00  --res_prop_simpl_given                  true
% 0.73/1.00  --res_passive_queue_type                priority_queues
% 0.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.73/1.00  --res_passive_queues_freq               [15;5]
% 0.73/1.00  --res_forward_subs                      full
% 0.73/1.00  --res_backward_subs                     full
% 0.73/1.00  --res_forward_subs_resolution           true
% 0.73/1.00  --res_backward_subs_resolution          true
% 0.73/1.00  --res_orphan_elimination                true
% 0.73/1.00  --res_time_limit                        2.
% 0.73/1.00  --res_out_proof                         true
% 0.73/1.00  
% 0.73/1.00  ------ Superposition Options
% 0.73/1.00  
% 0.73/1.00  --superposition_flag                    true
% 0.73/1.00  --sup_passive_queue_type                priority_queues
% 0.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.00  --demod_completeness_check              fast
% 0.73/1.00  --demod_use_ground                      true
% 0.73/1.00  --sup_to_prop_solver                    passive
% 0.73/1.00  --sup_prop_simpl_new                    true
% 0.73/1.00  --sup_prop_simpl_given                  true
% 0.73/1.00  --sup_fun_splitting                     false
% 0.73/1.00  --sup_smt_interval                      50000
% 0.73/1.00  
% 0.73/1.00  ------ Superposition Simplification Setup
% 0.73/1.00  
% 0.73/1.00  --sup_indices_passive                   []
% 0.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.00  --sup_full_bw                           [BwDemod]
% 0.73/1.00  --sup_immed_triv                        [TrivRules]
% 0.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.00  --sup_immed_bw_main                     []
% 0.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.00  
% 0.73/1.00  ------ Combination Options
% 0.73/1.00  
% 0.73/1.00  --comb_res_mult                         3
% 0.73/1.00  --comb_sup_mult                         2
% 0.73/1.00  --comb_inst_mult                        10
% 0.73/1.00  
% 0.73/1.00  ------ Debug Options
% 0.73/1.00  
% 0.73/1.00  --dbg_backtrace                         false
% 0.73/1.00  --dbg_dump_prop_clauses                 false
% 0.73/1.00  --dbg_dump_prop_clauses_file            -
% 0.73/1.00  --dbg_out_stat                          false
% 0.73/1.00  ------ Parsing...
% 0.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.73/1.00  
% 0.73/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.73/1.00  
% 0.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.73/1.00  
% 0.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.73/1.00  ------ Proving...
% 0.73/1.00  ------ Problem Properties 
% 0.73/1.00  
% 0.73/1.00  
% 0.73/1.00  clauses                                 7
% 0.73/1.00  conjectures                             1
% 0.73/1.00  EPR                                     1
% 0.73/1.00  Horn                                    7
% 0.73/1.00  unary                                   2
% 0.73/1.00  binary                                  1
% 0.73/1.00  lits                                    18
% 0.73/1.00  lits eq                                 7
% 0.73/1.00  fd_pure                                 0
% 0.73/1.00  fd_pseudo                               0
% 0.73/1.00  fd_cond                                 0
% 0.73/1.00  fd_pseudo_cond                          0
% 0.73/1.00  AC symbols                              0
% 0.73/1.00  
% 0.73/1.00  ------ Schedule dynamic 5 is on 
% 0.73/1.00  
% 0.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.73/1.00  
% 0.73/1.00  
% 0.73/1.00  ------ 
% 0.73/1.00  Current options:
% 0.73/1.00  ------ 
% 0.73/1.00  
% 0.73/1.00  ------ Input Options
% 0.73/1.00  
% 0.73/1.00  --out_options                           all
% 0.73/1.00  --tptp_safe_out                         true
% 0.73/1.00  --problem_path                          ""
% 0.73/1.00  --include_path                          ""
% 0.73/1.00  --clausifier                            res/vclausify_rel
% 0.73/1.00  --clausifier_options                    --mode clausify
% 0.73/1.00  --stdin                                 false
% 0.73/1.00  --stats_out                             all
% 0.73/1.00  
% 0.73/1.00  ------ General Options
% 0.73/1.00  
% 0.73/1.00  --fof                                   false
% 0.73/1.00  --time_out_real                         305.
% 0.73/1.00  --time_out_virtual                      -1.
% 0.73/1.00  --symbol_type_check                     false
% 0.73/1.00  --clausify_out                          false
% 0.73/1.00  --sig_cnt_out                           false
% 0.73/1.00  --trig_cnt_out                          false
% 0.73/1.00  --trig_cnt_out_tolerance                1.
% 0.73/1.00  --trig_cnt_out_sk_spl                   false
% 0.73/1.00  --abstr_cl_out                          false
% 0.73/1.00  
% 0.73/1.00  ------ Global Options
% 0.73/1.00  
% 0.73/1.00  --schedule                              default
% 0.73/1.00  --add_important_lit                     false
% 0.73/1.00  --prop_solver_per_cl                    1000
% 0.73/1.00  --min_unsat_core                        false
% 0.73/1.00  --soft_assumptions                      false
% 0.73/1.00  --soft_lemma_size                       3
% 0.73/1.00  --prop_impl_unit_size                   0
% 0.73/1.00  --prop_impl_unit                        []
% 0.73/1.00  --share_sel_clauses                     true
% 0.73/1.00  --reset_solvers                         false
% 0.73/1.00  --bc_imp_inh                            [conj_cone]
% 0.73/1.00  --conj_cone_tolerance                   3.
% 0.73/1.00  --extra_neg_conj                        none
% 0.73/1.00  --large_theory_mode                     true
% 0.73/1.00  --prolific_symb_bound                   200
% 0.73/1.00  --lt_threshold                          2000
% 0.73/1.00  --clause_weak_htbl                      true
% 0.73/1.00  --gc_record_bc_elim                     false
% 0.73/1.00  
% 0.73/1.00  ------ Preprocessing Options
% 0.73/1.00  
% 0.73/1.00  --preprocessing_flag                    true
% 0.73/1.00  --time_out_prep_mult                    0.1
% 0.73/1.00  --splitting_mode                        input
% 0.73/1.00  --splitting_grd                         true
% 0.73/1.00  --splitting_cvd                         false
% 0.73/1.00  --splitting_cvd_svl                     false
% 0.73/1.00  --splitting_nvd                         32
% 0.73/1.00  --sub_typing                            true
% 0.73/1.00  --prep_gs_sim                           true
% 0.73/1.00  --prep_unflatten                        true
% 0.73/1.00  --prep_res_sim                          true
% 0.73/1.00  --prep_upred                            true
% 0.73/1.00  --prep_sem_filter                       exhaustive
% 0.73/1.00  --prep_sem_filter_out                   false
% 0.73/1.00  --pred_elim                             true
% 0.73/1.00  --res_sim_input                         true
% 0.73/1.00  --eq_ax_congr_red                       true
% 0.73/1.00  --pure_diseq_elim                       true
% 0.73/1.00  --brand_transform                       false
% 0.73/1.00  --non_eq_to_eq                          false
% 0.73/1.00  --prep_def_merge                        true
% 0.73/1.00  --prep_def_merge_prop_impl              false
% 0.73/1.00  --prep_def_merge_mbd                    true
% 0.73/1.00  --prep_def_merge_tr_red                 false
% 0.73/1.00  --prep_def_merge_tr_cl                  false
% 0.73/1.00  --smt_preprocessing                     true
% 0.73/1.00  --smt_ac_axioms                         fast
% 0.73/1.00  --preprocessed_out                      false
% 0.73/1.00  --preprocessed_stats                    false
% 0.73/1.00  
% 0.73/1.00  ------ Abstraction refinement Options
% 0.73/1.00  
% 0.73/1.00  --abstr_ref                             []
% 0.73/1.00  --abstr_ref_prep                        false
% 0.73/1.00  --abstr_ref_until_sat                   false
% 0.73/1.00  --abstr_ref_sig_restrict                funpre
% 0.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.00  --abstr_ref_under                       []
% 0.73/1.00  
% 0.73/1.00  ------ SAT Options
% 0.73/1.00  
% 0.73/1.00  --sat_mode                              false
% 0.73/1.00  --sat_fm_restart_options                ""
% 0.73/1.00  --sat_gr_def                            false
% 0.73/1.00  --sat_epr_types                         true
% 0.73/1.00  --sat_non_cyclic_types                  false
% 0.73/1.00  --sat_finite_models                     false
% 0.73/1.00  --sat_fm_lemmas                         false
% 0.73/1.00  --sat_fm_prep                           false
% 0.73/1.00  --sat_fm_uc_incr                        true
% 0.73/1.00  --sat_out_model                         small
% 0.73/1.00  --sat_out_clauses                       false
% 0.73/1.00  
% 0.73/1.00  ------ QBF Options
% 0.73/1.00  
% 0.73/1.00  --qbf_mode                              false
% 0.73/1.00  --qbf_elim_univ                         false
% 0.73/1.00  --qbf_dom_inst                          none
% 0.73/1.00  --qbf_dom_pre_inst                      false
% 0.73/1.00  --qbf_sk_in                             false
% 0.73/1.00  --qbf_pred_elim                         true
% 0.73/1.00  --qbf_split                             512
% 0.73/1.00  
% 0.73/1.00  ------ BMC1 Options
% 0.73/1.00  
% 0.73/1.00  --bmc1_incremental                      false
% 0.73/1.00  --bmc1_axioms                           reachable_all
% 0.73/1.00  --bmc1_min_bound                        0
% 0.73/1.00  --bmc1_max_bound                        -1
% 0.73/1.00  --bmc1_max_bound_default                -1
% 0.73/1.00  --bmc1_symbol_reachability              true
% 0.73/1.00  --bmc1_property_lemmas                  false
% 0.73/1.00  --bmc1_k_induction                      false
% 0.73/1.00  --bmc1_non_equiv_states                 false
% 0.73/1.00  --bmc1_deadlock                         false
% 0.73/1.00  --bmc1_ucm                              false
% 0.73/1.00  --bmc1_add_unsat_core                   none
% 0.73/1.00  --bmc1_unsat_core_children              false
% 0.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.00  --bmc1_out_stat                         full
% 0.73/1.00  --bmc1_ground_init                      false
% 0.73/1.00  --bmc1_pre_inst_next_state              false
% 0.73/1.00  --bmc1_pre_inst_state                   false
% 0.73/1.00  --bmc1_pre_inst_reach_state             false
% 0.73/1.00  --bmc1_out_unsat_core                   false
% 0.73/1.00  --bmc1_aig_witness_out                  false
% 0.73/1.00  --bmc1_verbose                          false
% 0.73/1.00  --bmc1_dump_clauses_tptp                false
% 0.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.00  --bmc1_dump_file                        -
% 0.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.00  --bmc1_ucm_extend_mode                  1
% 0.73/1.00  --bmc1_ucm_init_mode                    2
% 0.73/1.00  --bmc1_ucm_cone_mode                    none
% 0.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.00  --bmc1_ucm_relax_model                  4
% 0.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.00  --bmc1_ucm_layered_model                none
% 0.73/1.00  --bmc1_ucm_max_lemma_size               10
% 0.73/1.00  
% 0.73/1.00  ------ AIG Options
% 0.73/1.00  
% 0.73/1.00  --aig_mode                              false
% 0.73/1.00  
% 0.73/1.00  ------ Instantiation Options
% 0.73/1.00  
% 0.73/1.00  --instantiation_flag                    true
% 0.73/1.00  --inst_sos_flag                         false
% 0.73/1.00  --inst_sos_phase                        true
% 0.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.00  --inst_lit_sel_side                     none
% 0.73/1.00  --inst_solver_per_active                1400
% 0.73/1.00  --inst_solver_calls_frac                1.
% 0.73/1.00  --inst_passive_queue_type               priority_queues
% 0.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.73/1.00  --inst_passive_queues_freq              [25;2]
% 0.73/1.00  --inst_dismatching                      true
% 0.73/1.00  --inst_eager_unprocessed_to_passive     true
% 0.73/1.00  --inst_prop_sim_given                   true
% 0.73/1.00  --inst_prop_sim_new                     false
% 0.73/1.00  --inst_subs_new                         false
% 0.73/1.00  --inst_eq_res_simp                      false
% 0.73/1.00  --inst_subs_given                       false
% 0.73/1.00  --inst_orphan_elimination               true
% 0.73/1.00  --inst_learning_loop_flag               true
% 0.73/1.00  --inst_learning_start                   3000
% 0.73/1.00  --inst_learning_factor                  2
% 0.73/1.00  --inst_start_prop_sim_after_learn       3
% 0.73/1.00  --inst_sel_renew                        solver
% 0.73/1.00  --inst_lit_activity_flag                true
% 0.73/1.00  --inst_restr_to_given                   false
% 0.73/1.00  --inst_activity_threshold               500
% 0.73/1.00  --inst_out_proof                        true
% 0.73/1.00  
% 0.73/1.00  ------ Resolution Options
% 0.73/1.00  
% 0.73/1.00  --resolution_flag                       false
% 0.73/1.00  --res_lit_sel                           adaptive
% 0.73/1.00  --res_lit_sel_side                      none
% 0.73/1.00  --res_ordering                          kbo
% 0.73/1.00  --res_to_prop_solver                    active
% 0.73/1.00  --res_prop_simpl_new                    false
% 0.73/1.00  --res_prop_simpl_given                  true
% 0.73/1.00  --res_passive_queue_type                priority_queues
% 0.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.73/1.00  --res_passive_queues_freq               [15;5]
% 0.73/1.00  --res_forward_subs                      full
% 0.73/1.00  --res_backward_subs                     full
% 0.73/1.00  --res_forward_subs_resolution           true
% 0.73/1.00  --res_backward_subs_resolution          true
% 0.73/1.00  --res_orphan_elimination                true
% 0.73/1.00  --res_time_limit                        2.
% 0.73/1.00  --res_out_proof                         true
% 0.73/1.00  
% 0.73/1.00  ------ Superposition Options
% 0.73/1.00  
% 0.73/1.00  --superposition_flag                    true
% 0.73/1.00  --sup_passive_queue_type                priority_queues
% 0.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.00  --demod_completeness_check              fast
% 0.73/1.00  --demod_use_ground                      true
% 0.73/1.00  --sup_to_prop_solver                    passive
% 0.73/1.00  --sup_prop_simpl_new                    true
% 0.73/1.00  --sup_prop_simpl_given                  true
% 0.73/1.00  --sup_fun_splitting                     false
% 0.73/1.00  --sup_smt_interval                      50000
% 0.73/1.00  
% 0.73/1.00  ------ Superposition Simplification Setup
% 0.73/1.00  
% 0.73/1.00  --sup_indices_passive                   []
% 0.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.00  --sup_full_bw                           [BwDemod]
% 0.73/1.00  --sup_immed_triv                        [TrivRules]
% 0.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.00  --sup_immed_bw_main                     []
% 0.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.00  
% 0.73/1.00  ------ Combination Options
% 0.73/1.00  
% 0.73/1.00  --comb_res_mult                         3
% 0.73/1.00  --comb_sup_mult                         2
% 0.73/1.00  --comb_inst_mult                        10
% 0.73/1.00  
% 0.73/1.00  ------ Debug Options
% 0.73/1.00  
% 0.73/1.00  --dbg_backtrace                         false
% 0.73/1.00  --dbg_dump_prop_clauses                 false
% 0.73/1.00  --dbg_dump_prop_clauses_file            -
% 0.73/1.00  --dbg_out_stat                          false
% 0.73/1.00  
% 0.73/1.00  
% 0.73/1.00  
% 0.73/1.00  
% 0.73/1.00  ------ Proving...
% 0.73/1.00  
% 0.73/1.00  
% 0.73/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 0.73/1.00  
% 0.73/1.00  % SZS output start Saturation for theBenchmark.p
% 0.73/1.00  
% 0.73/1.00  fof(f7,axiom,(
% 0.73/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f23,plain,(
% 0.73/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.73/1.00    inference(ennf_transformation,[],[f7])).
% 0.73/1.00  
% 0.73/1.00  fof(f24,plain,(
% 0.73/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.73/1.00    inference(flattening,[],[f23])).
% 0.73/1.00  
% 0.73/1.00  fof(f38,plain,(
% 0.73/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f24])).
% 0.73/1.00  
% 0.73/1.00  fof(f6,axiom,(
% 0.73/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f21,plain,(
% 0.73/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.73/1.00    inference(ennf_transformation,[],[f6])).
% 0.73/1.00  
% 0.73/1.00  fof(f22,plain,(
% 0.73/1.00    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.73/1.00    inference(flattening,[],[f21])).
% 0.73/1.00  
% 0.73/1.00  fof(f37,plain,(
% 0.73/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f22])).
% 0.73/1.00  
% 0.73/1.00  fof(f5,axiom,(
% 0.73/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f19,plain,(
% 0.73/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.73/1.00    inference(ennf_transformation,[],[f5])).
% 0.73/1.00  
% 0.73/1.00  fof(f20,plain,(
% 0.73/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.73/1.00    inference(flattening,[],[f19])).
% 0.73/1.00  
% 0.73/1.00  fof(f35,plain,(
% 0.73/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f20])).
% 0.73/1.00  
% 0.73/1.00  fof(f36,plain,(
% 0.73/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f20])).
% 0.73/1.00  
% 0.73/1.00  fof(f3,axiom,(
% 0.73/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f15,plain,(
% 0.73/1.00    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.73/1.00    inference(ennf_transformation,[],[f3])).
% 0.73/1.00  
% 0.73/1.00  fof(f16,plain,(
% 0.73/1.00    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.73/1.00    inference(flattening,[],[f15])).
% 0.73/1.00  
% 0.73/1.00  fof(f32,plain,(
% 0.73/1.00    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f16])).
% 0.73/1.00  
% 0.73/1.00  fof(f2,axiom,(
% 0.73/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f31,plain,(
% 0.73/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.73/1.00    inference(cnf_transformation,[],[f2])).
% 0.73/1.00  
% 0.73/1.00  fof(f1,axiom,(
% 0.73/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f14,plain,(
% 0.73/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.73/1.00    inference(ennf_transformation,[],[f1])).
% 0.73/1.00  
% 0.73/1.00  fof(f30,plain,(
% 0.73/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f14])).
% 0.73/1.00  
% 0.73/1.00  fof(f9,conjecture,(
% 0.73/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f10,negated_conjecture,(
% 0.73/1.00    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 0.73/1.00    inference(negated_conjecture,[],[f9])).
% 0.73/1.00  
% 0.73/1.00  fof(f11,plain,(
% 0.73/1.00    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 0.73/1.00    inference(pure_predicate_removal,[],[f10])).
% 0.73/1.00  
% 0.73/1.00  fof(f12,plain,(
% 0.73/1.00    ~! [X0] : (~v2_struct_0(X0) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 0.73/1.00    inference(pure_predicate_removal,[],[f11])).
% 0.73/1.00  
% 0.73/1.00  fof(f13,plain,(
% 0.73/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))),
% 0.73/1.00    inference(pure_predicate_removal,[],[f12])).
% 0.73/1.00  
% 0.73/1.00  fof(f26,plain,(
% 0.73/1.00    ? [X0,X1,X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))),
% 0.73/1.00    inference(ennf_transformation,[],[f13])).
% 0.73/1.00  
% 0.73/1.00  fof(f27,plain,(
% 0.73/1.00    ? [X0,X1,X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))),
% 0.73/1.00    inference(flattening,[],[f26])).
% 0.73/1.00  
% 0.73/1.00  fof(f28,plain,(
% 0.73/1.00    ? [X0,X1,X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.73/1.00    introduced(choice_axiom,[])).
% 0.73/1.00  
% 0.73/1.00  fof(f29,plain,(
% 0.73/1.00    (k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)),
% 0.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 0.73/1.00  
% 0.73/1.00  fof(f42,plain,(
% 0.73/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.73/1.00    inference(cnf_transformation,[],[f29])).
% 0.73/1.00  
% 0.73/1.00  fof(f43,plain,(
% 0.73/1.00    k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.73/1.00    inference(cnf_transformation,[],[f29])).
% 0.73/1.00  
% 0.73/1.00  fof(f41,plain,(
% 0.73/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.73/1.00    inference(cnf_transformation,[],[f29])).
% 0.73/1.00  
% 0.73/1.00  fof(f40,plain,(
% 0.73/1.00    v1_funct_1(sK2)),
% 0.73/1.00    inference(cnf_transformation,[],[f29])).
% 0.73/1.00  
% 0.73/1.00  fof(f8,axiom,(
% 0.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f25,plain,(
% 0.73/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.73/1.00    inference(ennf_transformation,[],[f8])).
% 0.73/1.00  
% 0.73/1.00  fof(f39,plain,(
% 0.73/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.73/1.00    inference(cnf_transformation,[],[f25])).
% 0.73/1.00  
% 0.73/1.00  fof(f4,axiom,(
% 0.73/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.73/1.00  
% 0.73/1.00  fof(f17,plain,(
% 0.73/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.73/1.00    inference(ennf_transformation,[],[f4])).
% 0.73/1.00  
% 0.73/1.00  fof(f18,plain,(
% 0.73/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.73/1.00    inference(flattening,[],[f17])).
% 0.73/1.00  
% 0.73/1.00  fof(f33,plain,(
% 0.73/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f18])).
% 0.73/1.00  
% 0.73/1.00  fof(f34,plain,(
% 0.73/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.73/1.00    inference(cnf_transformation,[],[f18])).
% 0.73/1.00  
% 0.73/1.00  cnf(c_144,plain,
% 0.73/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 0.73/1.00      | v1_funct_2(X3,X4,X5)
% 0.73/1.00      | X3 != X0
% 0.73/1.00      | X4 != X1
% 0.73/1.00      | X5 != X2 ),
% 0.73/1.00      theory(equality) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_139,plain,
% 0.73/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 0.73/1.00      theory(equality) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_136,plain,
% 0.73/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.73/1.00      theory(equality) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_284,plain,( X0_2 = X0_2 ),theory(equality) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_8,plain,
% 0.73/1.00      ( ~ v1_funct_1(X0)
% 0.73/1.00      | ~ v2_funct_1(X0)
% 0.73/1.00      | ~ v1_relat_1(X0)
% 0.73/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 0.73/1.00      inference(cnf_transformation,[],[f38]) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_7,plain,
% 0.73/1.00      ( ~ v1_funct_1(X0)
% 0.73/1.00      | ~ v2_funct_1(X0)
% 0.73/1.00      | v2_funct_1(k2_funct_1(X0))
% 0.73/1.00      | ~ v1_relat_1(X0) ),
% 0.73/1.00      inference(cnf_transformation,[],[f37]) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_6,plain,
% 0.73/1.00      ( ~ v1_funct_1(X0)
% 0.73/1.00      | ~ v2_funct_1(X0)
% 0.73/1.00      | ~ v1_relat_1(X0)
% 0.73/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.73/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_5,plain,
% 0.73/1.00      ( ~ v1_funct_1(X0)
% 0.73/1.00      | ~ v2_funct_1(X0)
% 0.73/1.00      | ~ v1_relat_1(X0)
% 0.73/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 0.73/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_2,plain,
% 0.73/1.00      ( ~ v1_funct_1(X0)
% 0.73/1.00      | ~ v2_funct_1(X0)
% 0.73/1.00      | ~ v1_relat_1(X0)
% 0.73/1.00      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 0.73/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_1,plain,
% 0.73/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.73/1.00      inference(cnf_transformation,[],[f31]) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_283,plain,
% 0.73/1.00      ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
% 0.73/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 0.73/1.00  
% 0.73/1.00  cnf(c_422,plain,
% 0.73/1.00      ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) = iProver_top ),
% 0.73/1.00      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_0,plain,
% 0.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_11,negated_conjecture,
% 0.83/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 0.83/1.00      inference(cnf_transformation,[],[f42]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_178,plain,
% 0.83/1.00      ( ~ v1_relat_1(X0)
% 0.83/1.00      | v1_relat_1(X1)
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 0.83/1.00      | sK2 != X1 ),
% 0.83/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_179,plain,
% 0.83/1.00      ( ~ v1_relat_1(X0)
% 0.83/1.00      | v1_relat_1(sK2)
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 0.83/1.00      inference(unflattening,[status(thm)],[c_178]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_279,plain,
% 0.83/1.00      ( ~ v1_relat_1(X0_44)
% 0.83/1.00      | v1_relat_1(sK2)
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_44) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_179]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_426,plain,
% 0.83/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_44)
% 0.83/1.00      | v1_relat_1(X0_44) != iProver_top
% 0.83/1.00      | v1_relat_1(sK2) = iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_519,plain,
% 0.83/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 0.83/1.00      | v1_relat_1(sK2) = iProver_top ),
% 0.83/1.00      inference(equality_resolution,[status(thm)],[c_426]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_605,plain,
% 0.83/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 0.83/1.00      inference(superposition,[status(thm)],[c_422,c_519]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_10,negated_conjecture,
% 0.83/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.83/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.83/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.83/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f43]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_12,negated_conjecture,
% 0.83/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 0.83/1.00      inference(cnf_transformation,[],[f41]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_154,plain,
% 0.83/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.83/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.83/1.00      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.83/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.83/1.00      | k2_funct_1(sK2) != sK2 ),
% 0.83/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_200,plain,
% 0.83/1.00      ( ~ v1_funct_1(k2_funct_1(sK2))
% 0.83/1.00      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.83/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.83/1.00      | k2_funct_1(sK2) != sK2
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 0.83/1.00      inference(resolution_lifted,[status(thm)],[c_154,c_11]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_277,plain,
% 0.83/1.00      ( ~ v1_funct_1(k2_funct_1(sK2))
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 0.83/1.00      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.83/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.83/1.00      | k2_funct_1(sK2) != sK2 ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_200]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_427,plain,
% 0.83/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 0.83/1.00      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.83/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.83/1.00      | k2_funct_1(sK2) != sK2
% 0.83/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_13,negated_conjecture,
% 0.83/1.00      ( v1_funct_1(sK2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f40]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_295,plain,
% 0.83/1.00      ( ~ v1_funct_1(X0_44) | v1_funct_1(X1_44) | X1_44 != X0_44 ),
% 0.83/1.00      theory(equality) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_507,plain,
% 0.83/1.00      ( ~ v1_funct_1(X0_44)
% 0.83/1.00      | v1_funct_1(k2_funct_1(sK2))
% 0.83/1.00      | k2_funct_1(sK2) != X0_44 ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_295]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_509,plain,
% 0.83/1.00      ( v1_funct_1(k2_funct_1(sK2))
% 0.83/1.00      | ~ v1_funct_1(sK2)
% 0.83/1.00      | k2_funct_1(sK2) != sK2 ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_507]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_561,plain,
% 0.83/1.00      ( k2_funct_1(sK2) != sK2
% 0.83/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.83/1.00      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 0.83/1.00      inference(global_propositional_subsumption,
% 0.83/1.00                [status(thm)],
% 0.83/1.00                [c_427,c_13,c_277,c_509]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_562,plain,
% 0.83/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 0.83/1.00      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.83/1.00      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.83/1.00      | k2_funct_1(sK2) != sK2 ),
% 0.83/1.00      inference(renaming,[status(thm)],[c_561]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_9,plain,
% 0.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.83/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f39]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_191,plain,
% 0.83/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.83/1.00      | sK2 != X2 ),
% 0.83/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_192,plain,
% 0.83/1.00      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 0.83/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.83/1.00      inference(unflattening,[status(thm)],[c_191]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_278,plain,
% 0.83/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))
% 0.83/1.00      | k2_relset_1(X0_45,X1_45,sK2) = k2_relat_1(sK2) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_192]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_499,plain,
% 0.83/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 0.83/1.00      inference(equality_resolution,[status(thm)],[c_278]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_4,plain,
% 0.83/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 0.83/1.00      inference(cnf_transformation,[],[f33]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_281,plain,
% 0.83/1.00      ( ~ v1_funct_1(X0_44)
% 0.83/1.00      | ~ v1_relat_1(X0_44)
% 0.83/1.00      | v1_relat_1(k2_funct_1(X0_44)) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_424,plain,
% 0.83/1.00      ( v1_funct_1(X0_44) != iProver_top
% 0.83/1.00      | v1_relat_1(X0_44) != iProver_top
% 0.83/1.00      | v1_relat_1(k2_funct_1(X0_44)) = iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_3,plain,
% 0.83/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_282,plain,
% 0.83/1.00      ( ~ v1_funct_1(X0_44)
% 0.83/1.00      | v1_funct_1(k2_funct_1(X0_44))
% 0.83/1.00      | ~ v1_relat_1(X0_44) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_423,plain,
% 0.83/1.00      ( v1_funct_1(X0_44) != iProver_top
% 0.83/1.00      | v1_funct_1(k2_funct_1(X0_44)) = iProver_top
% 0.83/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_280,negated_conjecture,
% 0.83/1.00      ( v1_funct_1(sK2) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_425,plain,
% 0.83/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  % SZS output end Saturation for theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  ------                               Statistics
% 0.83/1.00  
% 0.83/1.00  ------ General
% 0.83/1.00  
% 0.83/1.00  abstr_ref_over_cycles:                  0
% 0.83/1.00  abstr_ref_under_cycles:                 0
% 0.83/1.00  gc_basic_clause_elim:                   0
% 0.83/1.01  forced_gc_time:                         0
% 0.83/1.01  parsing_time:                           0.008
% 0.83/1.01  unif_index_cands_time:                  0.
% 0.83/1.01  unif_index_add_time:                    0.
% 0.83/1.01  orderings_time:                         0.
% 0.83/1.01  out_proof_time:                         0.
% 0.83/1.01  total_time:                             0.054
% 0.83/1.01  num_of_symbols:                         48
% 0.83/1.01  num_of_terms:                           651
% 0.83/1.01  
% 0.83/1.01  ------ Preprocessing
% 0.83/1.01  
% 0.83/1.01  num_of_splits:                          0
% 0.83/1.01  num_of_split_atoms:                     0
% 0.83/1.01  num_of_reused_defs:                     0
% 0.83/1.01  num_eq_ax_congr_red:                    9
% 0.83/1.01  num_of_sem_filtered_clauses:            6
% 0.83/1.01  num_of_subtypes:                        4
% 0.83/1.01  monotx_restored_types:                  0
% 0.83/1.01  sat_num_of_epr_types:                   0
% 0.83/1.01  sat_num_of_non_cyclic_types:            0
% 0.83/1.01  sat_guarded_non_collapsed_types:        0
% 0.83/1.01  num_pure_diseq_elim:                    0
% 0.83/1.01  simp_replaced_by:                       0
% 0.83/1.01  res_preprocessed:                       62
% 0.83/1.01  prep_upred:                             0
% 0.83/1.01  prep_unflattend:                        2
% 0.83/1.01  smt_new_axioms:                         0
% 0.83/1.01  pred_elim_cands:                        2
% 0.83/1.01  pred_elim:                              2
% 0.83/1.01  pred_elim_cl:                           2
% 0.83/1.01  pred_elim_cycles:                       4
% 0.83/1.01  merged_defs:                            0
% 0.83/1.01  merged_defs_ncl:                        0
% 0.83/1.01  bin_hyper_res:                          0
% 0.83/1.01  prep_cycles:                            4
% 0.83/1.01  pred_elim_time:                         0.002
% 0.83/1.01  splitting_time:                         0.
% 0.83/1.01  sem_filter_time:                        0.
% 0.83/1.01  monotx_time:                            0.
% 0.83/1.01  subtype_inf_time:                       0.
% 0.83/1.01  
% 0.83/1.01  ------ Problem properties
% 0.83/1.01  
% 0.83/1.01  clauses:                                7
% 0.83/1.01  conjectures:                            1
% 0.83/1.01  epr:                                    1
% 0.83/1.01  horn:                                   7
% 0.83/1.01  ground:                                 2
% 0.83/1.01  unary:                                  2
% 0.83/1.01  binary:                                 1
% 0.83/1.01  lits:                                   18
% 0.83/1.01  lits_eq:                                7
% 0.83/1.01  fd_pure:                                0
% 0.83/1.01  fd_pseudo:                              0
% 0.83/1.01  fd_cond:                                0
% 0.83/1.01  fd_pseudo_cond:                         0
% 0.83/1.01  ac_symbols:                             0
% 0.83/1.01  
% 0.83/1.01  ------ Propositional Solver
% 0.83/1.01  
% 0.83/1.01  prop_solver_calls:                      25
% 0.83/1.01  prop_fast_solver_calls:                 345
% 0.83/1.01  smt_solver_calls:                       0
% 0.83/1.01  smt_fast_solver_calls:                  0
% 0.83/1.01  prop_num_of_clauses:                    185
% 0.83/1.01  prop_preprocess_simplified:             1427
% 0.83/1.01  prop_fo_subsumed:                       1
% 0.83/1.01  prop_solver_time:                       0.
% 0.83/1.01  smt_solver_time:                        0.
% 0.83/1.01  smt_fast_solver_time:                   0.
% 0.83/1.01  prop_fast_solver_time:                  0.
% 0.83/1.01  prop_unsat_core_time:                   0.
% 0.83/1.01  
% 0.83/1.01  ------ QBF
% 0.83/1.01  
% 0.83/1.01  qbf_q_res:                              0
% 0.83/1.01  qbf_num_tautologies:                    0
% 0.83/1.01  qbf_prep_cycles:                        0
% 0.83/1.01  
% 0.83/1.01  ------ BMC1
% 0.83/1.01  
% 0.83/1.01  bmc1_current_bound:                     -1
% 0.83/1.01  bmc1_last_solved_bound:                 -1
% 0.83/1.01  bmc1_unsat_core_size:                   -1
% 0.83/1.01  bmc1_unsat_core_parents_size:           -1
% 0.83/1.01  bmc1_merge_next_fun:                    0
% 0.83/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.83/1.01  
% 0.83/1.01  ------ Instantiation
% 0.83/1.01  
% 0.83/1.01  inst_num_of_clauses:                    66
% 0.83/1.01  inst_num_in_passive:                    5
% 0.83/1.01  inst_num_in_active:                     51
% 0.83/1.01  inst_num_in_unprocessed:                10
% 0.83/1.01  inst_num_of_loops:                      60
% 0.83/1.01  inst_num_of_learning_restarts:          0
% 0.83/1.01  inst_num_moves_active_passive:          6
% 0.83/1.01  inst_lit_activity:                      0
% 0.83/1.01  inst_lit_activity_moves:                0
% 0.83/1.01  inst_num_tautologies:                   0
% 0.83/1.01  inst_num_prop_implied:                  0
% 0.83/1.01  inst_num_existing_simplified:           0
% 0.83/1.01  inst_num_eq_res_simplified:             0
% 0.83/1.01  inst_num_child_elim:                    0
% 0.83/1.01  inst_num_of_dismatching_blockings:      6
% 0.83/1.01  inst_num_of_non_proper_insts:           52
% 0.83/1.01  inst_num_of_duplicates:                 0
% 0.83/1.01  inst_inst_num_from_inst_to_res:         0
% 0.83/1.01  inst_dismatching_checking_time:         0.
% 0.83/1.01  
% 0.83/1.01  ------ Resolution
% 0.83/1.01  
% 0.83/1.01  res_num_of_clauses:                     0
% 0.83/1.01  res_num_in_passive:                     0
% 0.83/1.01  res_num_in_active:                      0
% 0.83/1.01  res_num_of_loops:                       66
% 0.83/1.01  res_forward_subset_subsumed:            14
% 0.83/1.01  res_backward_subset_subsumed:           0
% 0.83/1.01  res_forward_subsumed:                   0
% 0.83/1.01  res_backward_subsumed:                  0
% 0.83/1.01  res_forward_subsumption_resolution:     0
% 0.83/1.01  res_backward_subsumption_resolution:    0
% 0.83/1.01  res_clause_to_clause_subsumption:       8
% 0.83/1.01  res_orphan_elimination:                 0
% 0.83/1.01  res_tautology_del:                      6
% 0.83/1.01  res_num_eq_res_simplified:              0
% 0.83/1.01  res_num_sel_changes:                    0
% 0.83/1.01  res_moves_from_active_to_pass:          0
% 0.83/1.01  
% 0.83/1.01  ------ Superposition
% 0.83/1.01  
% 0.83/1.01  sup_time_total:                         0.
% 0.83/1.01  sup_time_generating:                    0.
% 0.83/1.01  sup_time_sim_full:                      0.
% 0.83/1.01  sup_time_sim_immed:                     0.
% 0.83/1.01  
% 0.83/1.01  sup_num_of_clauses:                     10
% 0.83/1.01  sup_num_in_active:                      10
% 0.83/1.01  sup_num_in_passive:                     0
% 0.83/1.01  sup_num_of_loops:                       10
% 0.83/1.01  sup_fw_superposition:                   0
% 0.83/1.01  sup_bw_superposition:                   1
% 0.83/1.01  sup_immediate_simplified:               0
% 0.83/1.01  sup_given_eliminated:                   0
% 0.83/1.01  comparisons_done:                       0
% 0.83/1.01  comparisons_avoided:                    0
% 0.83/1.01  
% 0.83/1.01  ------ Simplifications
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  sim_fw_subset_subsumed:                 0
% 0.83/1.01  sim_bw_subset_subsumed:                 0
% 0.83/1.01  sim_fw_subsumed:                        0
% 0.83/1.01  sim_bw_subsumed:                        0
% 0.83/1.01  sim_fw_subsumption_res:                 0
% 0.83/1.01  sim_bw_subsumption_res:                 0
% 0.83/1.01  sim_tautology_del:                      0
% 0.83/1.01  sim_eq_tautology_del:                   0
% 0.83/1.01  sim_eq_res_simp:                        0
% 0.83/1.01  sim_fw_demodulated:                     0
% 0.83/1.01  sim_bw_demodulated:                     0
% 0.83/1.01  sim_light_normalised:                   0
% 0.83/1.01  sim_joinable_taut:                      0
% 0.83/1.01  sim_joinable_simp:                      0
% 0.83/1.01  sim_ac_normalised:                      0
% 0.83/1.01  sim_smt_subsumption:                    0
% 0.83/1.01  
%------------------------------------------------------------------------------
