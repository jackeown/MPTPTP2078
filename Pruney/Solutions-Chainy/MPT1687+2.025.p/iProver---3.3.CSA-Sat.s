%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:17 EST 2020

% Result     : CounterSatisfiable 0.92s
% Output     : Saturation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   53 (  97 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 603 expanded)
%              Number of equality atoms :   51 (  91 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
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
    inference(pure_predicate_removal,[],[f6])).

fof(f8,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
       => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
          & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_funct_1(X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
        | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
        | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,
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

fof(f19,plain,
    ( ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_106,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_103,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_100,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_99,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_98,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_94,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_152,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_153,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_189,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))
    | k2_relset_1(X0_42,X1_42,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_230,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_189])).

cnf(c_6,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_112,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_8,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_132,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_112,c_8])).

cnf(c_161,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_132,c_7])).

cnf(c_188,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_161])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.92/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.92/1.07  
% 0.92/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.92/1.07  
% 0.92/1.07  ------  iProver source info
% 0.92/1.07  
% 0.92/1.07  git: date: 2020-06-30 10:37:57 +0100
% 0.92/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.92/1.07  git: non_committed_changes: false
% 0.92/1.07  git: last_make_outside_of_git: false
% 0.92/1.07  
% 0.92/1.07  ------ 
% 0.92/1.07  
% 0.92/1.07  ------ Input Options
% 0.92/1.07  
% 0.92/1.07  --out_options                           all
% 0.92/1.07  --tptp_safe_out                         true
% 0.92/1.07  --problem_path                          ""
% 0.92/1.07  --include_path                          ""
% 0.92/1.07  --clausifier                            res/vclausify_rel
% 0.92/1.07  --clausifier_options                    --mode clausify
% 0.92/1.07  --stdin                                 false
% 0.92/1.07  --stats_out                             all
% 0.92/1.07  
% 0.92/1.07  ------ General Options
% 0.92/1.07  
% 0.92/1.07  --fof                                   false
% 0.92/1.07  --time_out_real                         305.
% 0.92/1.07  --time_out_virtual                      -1.
% 0.92/1.07  --symbol_type_check                     false
% 0.92/1.07  --clausify_out                          false
% 0.92/1.07  --sig_cnt_out                           false
% 0.92/1.07  --trig_cnt_out                          false
% 0.92/1.07  --trig_cnt_out_tolerance                1.
% 0.92/1.07  --trig_cnt_out_sk_spl                   false
% 0.92/1.07  --abstr_cl_out                          false
% 0.92/1.07  
% 0.92/1.07  ------ Global Options
% 0.92/1.07  
% 0.92/1.07  --schedule                              default
% 0.92/1.07  --add_important_lit                     false
% 0.92/1.07  --prop_solver_per_cl                    1000
% 0.92/1.07  --min_unsat_core                        false
% 0.92/1.07  --soft_assumptions                      false
% 0.92/1.07  --soft_lemma_size                       3
% 0.92/1.07  --prop_impl_unit_size                   0
% 0.92/1.07  --prop_impl_unit                        []
% 0.92/1.07  --share_sel_clauses                     true
% 0.92/1.07  --reset_solvers                         false
% 0.92/1.07  --bc_imp_inh                            [conj_cone]
% 0.92/1.07  --conj_cone_tolerance                   3.
% 0.92/1.07  --extra_neg_conj                        none
% 0.92/1.07  --large_theory_mode                     true
% 0.92/1.07  --prolific_symb_bound                   200
% 0.92/1.07  --lt_threshold                          2000
% 0.92/1.07  --clause_weak_htbl                      true
% 0.92/1.07  --gc_record_bc_elim                     false
% 0.92/1.07  
% 0.92/1.07  ------ Preprocessing Options
% 0.92/1.07  
% 0.92/1.07  --preprocessing_flag                    true
% 0.92/1.07  --time_out_prep_mult                    0.1
% 0.92/1.07  --splitting_mode                        input
% 0.92/1.07  --splitting_grd                         true
% 0.92/1.07  --splitting_cvd                         false
% 0.92/1.07  --splitting_cvd_svl                     false
% 0.92/1.07  --splitting_nvd                         32
% 0.92/1.07  --sub_typing                            true
% 0.92/1.07  --prep_gs_sim                           true
% 0.92/1.07  --prep_unflatten                        true
% 0.92/1.07  --prep_res_sim                          true
% 0.92/1.07  --prep_upred                            true
% 0.92/1.07  --prep_sem_filter                       exhaustive
% 0.92/1.07  --prep_sem_filter_out                   false
% 0.92/1.07  --pred_elim                             true
% 0.92/1.07  --res_sim_input                         true
% 0.92/1.07  --eq_ax_congr_red                       true
% 0.92/1.07  --pure_diseq_elim                       true
% 0.92/1.07  --brand_transform                       false
% 0.92/1.07  --non_eq_to_eq                          false
% 0.92/1.07  --prep_def_merge                        true
% 0.92/1.07  --prep_def_merge_prop_impl              false
% 0.92/1.07  --prep_def_merge_mbd                    true
% 0.92/1.07  --prep_def_merge_tr_red                 false
% 0.92/1.07  --prep_def_merge_tr_cl                  false
% 0.92/1.07  --smt_preprocessing                     true
% 0.92/1.07  --smt_ac_axioms                         fast
% 0.92/1.07  --preprocessed_out                      false
% 0.92/1.07  --preprocessed_stats                    false
% 0.92/1.07  
% 0.92/1.07  ------ Abstraction refinement Options
% 0.92/1.07  
% 0.92/1.07  --abstr_ref                             []
% 0.92/1.07  --abstr_ref_prep                        false
% 0.92/1.07  --abstr_ref_until_sat                   false
% 0.92/1.07  --abstr_ref_sig_restrict                funpre
% 0.92/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/1.07  --abstr_ref_under                       []
% 0.92/1.07  
% 0.92/1.07  ------ SAT Options
% 0.92/1.07  
% 0.92/1.07  --sat_mode                              false
% 0.92/1.07  --sat_fm_restart_options                ""
% 0.92/1.07  --sat_gr_def                            false
% 0.92/1.07  --sat_epr_types                         true
% 0.92/1.07  --sat_non_cyclic_types                  false
% 0.92/1.07  --sat_finite_models                     false
% 0.92/1.07  --sat_fm_lemmas                         false
% 0.92/1.07  --sat_fm_prep                           false
% 0.92/1.07  --sat_fm_uc_incr                        true
% 0.92/1.07  --sat_out_model                         small
% 0.92/1.07  --sat_out_clauses                       false
% 0.92/1.07  
% 0.92/1.07  ------ QBF Options
% 0.92/1.07  
% 0.92/1.07  --qbf_mode                              false
% 0.92/1.07  --qbf_elim_univ                         false
% 0.92/1.07  --qbf_dom_inst                          none
% 0.92/1.07  --qbf_dom_pre_inst                      false
% 0.92/1.07  --qbf_sk_in                             false
% 0.92/1.07  --qbf_pred_elim                         true
% 0.92/1.07  --qbf_split                             512
% 0.92/1.07  
% 0.92/1.07  ------ BMC1 Options
% 0.92/1.07  
% 0.92/1.07  --bmc1_incremental                      false
% 0.92/1.07  --bmc1_axioms                           reachable_all
% 0.92/1.07  --bmc1_min_bound                        0
% 0.92/1.07  --bmc1_max_bound                        -1
% 0.92/1.07  --bmc1_max_bound_default                -1
% 0.92/1.07  --bmc1_symbol_reachability              true
% 0.92/1.07  --bmc1_property_lemmas                  false
% 0.92/1.07  --bmc1_k_induction                      false
% 0.92/1.07  --bmc1_non_equiv_states                 false
% 0.92/1.07  --bmc1_deadlock                         false
% 0.92/1.07  --bmc1_ucm                              false
% 0.92/1.07  --bmc1_add_unsat_core                   none
% 0.92/1.07  --bmc1_unsat_core_children              false
% 0.92/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/1.07  --bmc1_out_stat                         full
% 0.92/1.07  --bmc1_ground_init                      false
% 0.92/1.07  --bmc1_pre_inst_next_state              false
% 0.92/1.07  --bmc1_pre_inst_state                   false
% 0.92/1.07  --bmc1_pre_inst_reach_state             false
% 0.92/1.07  --bmc1_out_unsat_core                   false
% 0.92/1.07  --bmc1_aig_witness_out                  false
% 0.92/1.07  --bmc1_verbose                          false
% 0.92/1.07  --bmc1_dump_clauses_tptp                false
% 0.92/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.92/1.07  --bmc1_dump_file                        -
% 0.92/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.92/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.92/1.07  --bmc1_ucm_extend_mode                  1
% 0.92/1.07  --bmc1_ucm_init_mode                    2
% 0.92/1.07  --bmc1_ucm_cone_mode                    none
% 0.92/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.92/1.07  --bmc1_ucm_relax_model                  4
% 0.92/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.92/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/1.07  --bmc1_ucm_layered_model                none
% 0.92/1.07  --bmc1_ucm_max_lemma_size               10
% 0.92/1.07  
% 0.92/1.07  ------ AIG Options
% 0.92/1.07  
% 0.92/1.07  --aig_mode                              false
% 0.92/1.07  
% 0.92/1.07  ------ Instantiation Options
% 0.92/1.07  
% 0.92/1.07  --instantiation_flag                    true
% 0.92/1.07  --inst_sos_flag                         false
% 0.92/1.07  --inst_sos_phase                        true
% 0.92/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/1.07  --inst_lit_sel_side                     num_symb
% 0.92/1.07  --inst_solver_per_active                1400
% 0.92/1.07  --inst_solver_calls_frac                1.
% 0.92/1.07  --inst_passive_queue_type               priority_queues
% 0.92/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.92/1.07  --inst_passive_queues_freq              [25;2]
% 0.92/1.07  --inst_dismatching                      true
% 0.92/1.07  --inst_eager_unprocessed_to_passive     true
% 0.92/1.07  --inst_prop_sim_given                   true
% 0.92/1.07  --inst_prop_sim_new                     false
% 0.92/1.07  --inst_subs_new                         false
% 0.92/1.07  --inst_eq_res_simp                      false
% 0.92/1.07  --inst_subs_given                       false
% 0.92/1.07  --inst_orphan_elimination               true
% 0.92/1.07  --inst_learning_loop_flag               true
% 0.92/1.07  --inst_learning_start                   3000
% 0.92/1.07  --inst_learning_factor                  2
% 0.92/1.07  --inst_start_prop_sim_after_learn       3
% 0.92/1.07  --inst_sel_renew                        solver
% 0.92/1.07  --inst_lit_activity_flag                true
% 0.92/1.07  --inst_restr_to_given                   false
% 0.92/1.07  --inst_activity_threshold               500
% 0.92/1.07  --inst_out_proof                        true
% 0.92/1.07  
% 0.92/1.07  ------ Resolution Options
% 0.92/1.07  
% 0.92/1.07  --resolution_flag                       true
% 0.92/1.07  --res_lit_sel                           adaptive
% 0.92/1.07  --res_lit_sel_side                      none
% 0.92/1.07  --res_ordering                          kbo
% 0.92/1.07  --res_to_prop_solver                    active
% 0.92/1.07  --res_prop_simpl_new                    false
% 0.92/1.07  --res_prop_simpl_given                  true
% 0.92/1.07  --res_passive_queue_type                priority_queues
% 0.92/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.92/1.07  --res_passive_queues_freq               [15;5]
% 0.92/1.07  --res_forward_subs                      full
% 0.92/1.07  --res_backward_subs                     full
% 0.92/1.07  --res_forward_subs_resolution           true
% 0.92/1.07  --res_backward_subs_resolution          true
% 0.92/1.07  --res_orphan_elimination                true
% 0.92/1.07  --res_time_limit                        2.
% 0.92/1.07  --res_out_proof                         true
% 0.92/1.07  
% 0.92/1.07  ------ Superposition Options
% 0.92/1.07  
% 0.92/1.07  --superposition_flag                    true
% 0.92/1.07  --sup_passive_queue_type                priority_queues
% 0.92/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.92/1.07  --demod_completeness_check              fast
% 0.92/1.07  --demod_use_ground                      true
% 0.92/1.07  --sup_to_prop_solver                    passive
% 0.92/1.07  --sup_prop_simpl_new                    true
% 0.92/1.07  --sup_prop_simpl_given                  true
% 0.92/1.07  --sup_fun_splitting                     false
% 0.92/1.07  --sup_smt_interval                      50000
% 0.92/1.07  
% 0.92/1.07  ------ Superposition Simplification Setup
% 0.92/1.07  
% 0.92/1.07  --sup_indices_passive                   []
% 0.92/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.07  --sup_full_bw                           [BwDemod]
% 0.92/1.07  --sup_immed_triv                        [TrivRules]
% 0.92/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.07  --sup_immed_bw_main                     []
% 0.92/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.07  
% 0.92/1.07  ------ Combination Options
% 0.92/1.07  
% 0.92/1.07  --comb_res_mult                         3
% 0.92/1.07  --comb_sup_mult                         2
% 0.92/1.07  --comb_inst_mult                        10
% 0.92/1.07  
% 0.92/1.07  ------ Debug Options
% 0.92/1.07  
% 0.92/1.07  --dbg_backtrace                         false
% 0.92/1.07  --dbg_dump_prop_clauses                 false
% 0.92/1.07  --dbg_dump_prop_clauses_file            -
% 0.92/1.07  --dbg_out_stat                          false
% 0.92/1.07  ------ Parsing...
% 0.92/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.92/1.07  
% 0.92/1.07  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.92/1.07  
% 0.92/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.92/1.07  
% 0.92/1.07  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.92/1.07  ------ Proving...
% 0.92/1.07  ------ Problem Properties 
% 0.92/1.07  
% 0.92/1.07  
% 0.92/1.07  clauses                                 2
% 0.92/1.07  conjectures                             0
% 0.92/1.07  EPR                                     0
% 0.92/1.07  Horn                                    2
% 0.92/1.07  unary                                   0
% 0.92/1.07  binary                                  1
% 0.92/1.07  lits                                    6
% 0.92/1.07  lits eq                                 6
% 0.92/1.07  fd_pure                                 0
% 0.92/1.07  fd_pseudo                               0
% 0.92/1.07  fd_cond                                 0
% 0.92/1.07  fd_pseudo_cond                          0
% 0.92/1.07  AC symbols                              0
% 0.92/1.07  
% 0.92/1.07  ------ Schedule dynamic 5 is on 
% 0.92/1.07  
% 0.92/1.07  ------ no conjectures: strip conj schedule 
% 0.92/1.07  
% 0.92/1.07  ------ pure equality problem: resolution off 
% 0.92/1.07  
% 0.92/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.92/1.07  
% 0.92/1.07  
% 0.92/1.07  ------ 
% 0.92/1.07  Current options:
% 0.92/1.07  ------ 
% 0.92/1.07  
% 0.92/1.07  ------ Input Options
% 0.92/1.07  
% 0.92/1.07  --out_options                           all
% 0.92/1.07  --tptp_safe_out                         true
% 0.92/1.07  --problem_path                          ""
% 0.92/1.07  --include_path                          ""
% 0.92/1.07  --clausifier                            res/vclausify_rel
% 0.92/1.07  --clausifier_options                    --mode clausify
% 0.92/1.07  --stdin                                 false
% 0.92/1.07  --stats_out                             all
% 0.92/1.07  
% 0.92/1.07  ------ General Options
% 0.92/1.07  
% 0.92/1.07  --fof                                   false
% 0.92/1.07  --time_out_real                         305.
% 0.92/1.07  --time_out_virtual                      -1.
% 0.92/1.07  --symbol_type_check                     false
% 0.92/1.07  --clausify_out                          false
% 0.92/1.07  --sig_cnt_out                           false
% 0.92/1.07  --trig_cnt_out                          false
% 0.92/1.07  --trig_cnt_out_tolerance                1.
% 0.92/1.07  --trig_cnt_out_sk_spl                   false
% 0.92/1.07  --abstr_cl_out                          false
% 0.92/1.07  
% 0.92/1.07  ------ Global Options
% 0.92/1.07  
% 0.92/1.07  --schedule                              default
% 0.92/1.07  --add_important_lit                     false
% 0.92/1.07  --prop_solver_per_cl                    1000
% 0.92/1.07  --min_unsat_core                        false
% 0.92/1.07  --soft_assumptions                      false
% 0.92/1.07  --soft_lemma_size                       3
% 0.92/1.07  --prop_impl_unit_size                   0
% 0.92/1.07  --prop_impl_unit                        []
% 0.92/1.07  --share_sel_clauses                     true
% 0.92/1.07  --reset_solvers                         false
% 0.92/1.07  --bc_imp_inh                            [conj_cone]
% 0.92/1.07  --conj_cone_tolerance                   3.
% 0.92/1.07  --extra_neg_conj                        none
% 0.92/1.07  --large_theory_mode                     true
% 0.92/1.07  --prolific_symb_bound                   200
% 0.92/1.07  --lt_threshold                          2000
% 0.92/1.07  --clause_weak_htbl                      true
% 0.92/1.07  --gc_record_bc_elim                     false
% 0.92/1.07  
% 0.92/1.07  ------ Preprocessing Options
% 0.92/1.07  
% 0.92/1.07  --preprocessing_flag                    true
% 0.92/1.07  --time_out_prep_mult                    0.1
% 0.92/1.07  --splitting_mode                        input
% 0.92/1.07  --splitting_grd                         true
% 0.92/1.07  --splitting_cvd                         false
% 0.92/1.07  --splitting_cvd_svl                     false
% 0.92/1.07  --splitting_nvd                         32
% 0.92/1.07  --sub_typing                            true
% 0.92/1.07  --prep_gs_sim                           true
% 0.92/1.07  --prep_unflatten                        true
% 0.92/1.07  --prep_res_sim                          true
% 0.92/1.07  --prep_upred                            true
% 0.92/1.07  --prep_sem_filter                       exhaustive
% 0.92/1.07  --prep_sem_filter_out                   false
% 0.92/1.07  --pred_elim                             true
% 0.92/1.07  --res_sim_input                         true
% 0.92/1.07  --eq_ax_congr_red                       true
% 0.92/1.07  --pure_diseq_elim                       true
% 0.92/1.07  --brand_transform                       false
% 0.92/1.07  --non_eq_to_eq                          false
% 0.92/1.07  --prep_def_merge                        true
% 0.92/1.07  --prep_def_merge_prop_impl              false
% 0.92/1.07  --prep_def_merge_mbd                    true
% 0.92/1.07  --prep_def_merge_tr_red                 false
% 0.92/1.07  --prep_def_merge_tr_cl                  false
% 0.92/1.07  --smt_preprocessing                     true
% 0.92/1.07  --smt_ac_axioms                         fast
% 0.92/1.07  --preprocessed_out                      false
% 0.92/1.07  --preprocessed_stats                    false
% 0.92/1.07  
% 0.92/1.07  ------ Abstraction refinement Options
% 0.92/1.07  
% 0.92/1.07  --abstr_ref                             []
% 0.92/1.07  --abstr_ref_prep                        false
% 0.92/1.07  --abstr_ref_until_sat                   false
% 0.92/1.07  --abstr_ref_sig_restrict                funpre
% 0.92/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/1.07  --abstr_ref_under                       []
% 0.92/1.07  
% 0.92/1.07  ------ SAT Options
% 0.92/1.07  
% 0.92/1.07  --sat_mode                              false
% 0.92/1.07  --sat_fm_restart_options                ""
% 0.92/1.07  --sat_gr_def                            false
% 0.92/1.07  --sat_epr_types                         true
% 0.92/1.07  --sat_non_cyclic_types                  false
% 0.92/1.07  --sat_finite_models                     false
% 0.92/1.07  --sat_fm_lemmas                         false
% 0.92/1.07  --sat_fm_prep                           false
% 0.92/1.07  --sat_fm_uc_incr                        true
% 0.92/1.07  --sat_out_model                         small
% 0.92/1.07  --sat_out_clauses                       false
% 0.92/1.07  
% 0.92/1.07  ------ QBF Options
% 0.92/1.07  
% 0.92/1.07  --qbf_mode                              false
% 0.92/1.07  --qbf_elim_univ                         false
% 0.92/1.07  --qbf_dom_inst                          none
% 0.92/1.07  --qbf_dom_pre_inst                      false
% 0.92/1.07  --qbf_sk_in                             false
% 0.92/1.07  --qbf_pred_elim                         true
% 0.92/1.07  --qbf_split                             512
% 0.92/1.07  
% 0.92/1.07  ------ BMC1 Options
% 0.92/1.07  
% 0.92/1.07  --bmc1_incremental                      false
% 0.92/1.07  --bmc1_axioms                           reachable_all
% 0.92/1.07  --bmc1_min_bound                        0
% 0.92/1.07  --bmc1_max_bound                        -1
% 0.92/1.07  --bmc1_max_bound_default                -1
% 0.92/1.07  --bmc1_symbol_reachability              true
% 0.92/1.07  --bmc1_property_lemmas                  false
% 0.92/1.07  --bmc1_k_induction                      false
% 0.92/1.07  --bmc1_non_equiv_states                 false
% 0.92/1.07  --bmc1_deadlock                         false
% 0.92/1.07  --bmc1_ucm                              false
% 0.92/1.07  --bmc1_add_unsat_core                   none
% 0.92/1.07  --bmc1_unsat_core_children              false
% 0.92/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/1.07  --bmc1_out_stat                         full
% 0.92/1.07  --bmc1_ground_init                      false
% 0.92/1.07  --bmc1_pre_inst_next_state              false
% 0.92/1.07  --bmc1_pre_inst_state                   false
% 0.92/1.07  --bmc1_pre_inst_reach_state             false
% 0.92/1.07  --bmc1_out_unsat_core                   false
% 0.92/1.07  --bmc1_aig_witness_out                  false
% 0.92/1.07  --bmc1_verbose                          false
% 0.92/1.07  --bmc1_dump_clauses_tptp                false
% 0.92/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.92/1.07  --bmc1_dump_file                        -
% 0.92/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.92/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.92/1.07  --bmc1_ucm_extend_mode                  1
% 0.92/1.07  --bmc1_ucm_init_mode                    2
% 0.92/1.07  --bmc1_ucm_cone_mode                    none
% 0.92/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.92/1.07  --bmc1_ucm_relax_model                  4
% 0.92/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.92/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/1.07  --bmc1_ucm_layered_model                none
% 0.92/1.07  --bmc1_ucm_max_lemma_size               10
% 0.92/1.07  
% 0.92/1.07  ------ AIG Options
% 0.92/1.07  
% 0.92/1.07  --aig_mode                              false
% 0.92/1.07  
% 0.92/1.07  ------ Instantiation Options
% 0.92/1.07  
% 0.92/1.07  --instantiation_flag                    true
% 0.92/1.07  --inst_sos_flag                         false
% 0.92/1.07  --inst_sos_phase                        true
% 0.92/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/1.07  --inst_lit_sel_side                     none
% 0.92/1.07  --inst_solver_per_active                1400
% 0.92/1.07  --inst_solver_calls_frac                1.
% 0.92/1.07  --inst_passive_queue_type               priority_queues
% 0.92/1.07  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.92/1.07  --inst_passive_queues_freq              [25;2]
% 0.92/1.07  --inst_dismatching                      true
% 0.92/1.07  --inst_eager_unprocessed_to_passive     true
% 0.92/1.07  --inst_prop_sim_given                   true
% 0.92/1.07  --inst_prop_sim_new                     false
% 0.92/1.07  --inst_subs_new                         false
% 0.92/1.07  --inst_eq_res_simp                      false
% 0.92/1.07  --inst_subs_given                       false
% 0.92/1.07  --inst_orphan_elimination               true
% 0.92/1.07  --inst_learning_loop_flag               true
% 0.92/1.07  --inst_learning_start                   3000
% 0.92/1.07  --inst_learning_factor                  2
% 0.92/1.07  --inst_start_prop_sim_after_learn       3
% 0.92/1.07  --inst_sel_renew                        solver
% 0.92/1.07  --inst_lit_activity_flag                true
% 0.92/1.07  --inst_restr_to_given                   false
% 0.92/1.07  --inst_activity_threshold               500
% 0.92/1.07  --inst_out_proof                        true
% 0.92/1.07  
% 0.92/1.07  ------ Resolution Options
% 0.92/1.07  
% 0.92/1.07  --resolution_flag                       false
% 0.92/1.07  --res_lit_sel                           adaptive
% 0.92/1.07  --res_lit_sel_side                      none
% 0.92/1.07  --res_ordering                          kbo
% 0.92/1.07  --res_to_prop_solver                    active
% 0.92/1.07  --res_prop_simpl_new                    false
% 0.92/1.07  --res_prop_simpl_given                  true
% 0.92/1.07  --res_passive_queue_type                priority_queues
% 0.92/1.07  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.92/1.07  --res_passive_queues_freq               [15;5]
% 0.92/1.07  --res_forward_subs                      full
% 0.92/1.07  --res_backward_subs                     full
% 0.92/1.07  --res_forward_subs_resolution           true
% 0.92/1.07  --res_backward_subs_resolution          true
% 0.92/1.07  --res_orphan_elimination                true
% 0.92/1.07  --res_time_limit                        2.
% 0.92/1.07  --res_out_proof                         true
% 0.92/1.07  
% 0.92/1.07  ------ Superposition Options
% 0.92/1.07  
% 0.92/1.07  --superposition_flag                    true
% 0.92/1.07  --sup_passive_queue_type                priority_queues
% 0.92/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.92/1.07  --demod_completeness_check              fast
% 0.92/1.07  --demod_use_ground                      true
% 0.92/1.07  --sup_to_prop_solver                    passive
% 0.92/1.07  --sup_prop_simpl_new                    true
% 0.92/1.07  --sup_prop_simpl_given                  true
% 0.92/1.07  --sup_fun_splitting                     false
% 0.92/1.07  --sup_smt_interval                      50000
% 0.92/1.07  
% 0.92/1.07  ------ Superposition Simplification Setup
% 0.92/1.07  
% 0.92/1.07  --sup_indices_passive                   []
% 0.92/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.07  --sup_full_bw                           [BwDemod]
% 0.92/1.07  --sup_immed_triv                        [TrivRules]
% 0.92/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.07  --sup_immed_bw_main                     []
% 0.92/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.07  
% 0.92/1.07  ------ Combination Options
% 0.92/1.07  
% 0.92/1.07  --comb_res_mult                         3
% 0.92/1.07  --comb_sup_mult                         2
% 0.92/1.07  --comb_inst_mult                        10
% 0.92/1.07  
% 0.92/1.07  ------ Debug Options
% 0.92/1.07  
% 0.92/1.07  --dbg_backtrace                         false
% 0.92/1.07  --dbg_dump_prop_clauses                 false
% 0.92/1.07  --dbg_dump_prop_clauses_file            -
% 0.92/1.07  --dbg_out_stat                          false
% 0.92/1.07  
% 0.92/1.07  
% 0.92/1.07  
% 0.92/1.07  
% 0.92/1.07  ------ Proving...
% 0.92/1.07  
% 0.92/1.07  
% 0.92/1.07  % SZS status CounterSatisfiable for theBenchmark.p
% 0.92/1.07  
% 0.92/1.07  % SZS output start Saturation for theBenchmark.p
% 0.92/1.07  
% 0.92/1.07  fof(f3,axiom,(
% 0.92/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.92/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.07  
% 0.92/1.07  fof(f14,plain,(
% 0.92/1.07    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/1.07    inference(ennf_transformation,[],[f3])).
% 0.92/1.07  
% 0.92/1.07  fof(f24,plain,(
% 0.92/1.07    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/1.07    inference(cnf_transformation,[],[f14])).
% 0.92/1.07  
% 0.92/1.07  fof(f2,axiom,(
% 0.92/1.07    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.92/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.07  
% 0.92/1.07  fof(f12,plain,(
% 0.92/1.07    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.92/1.07    inference(ennf_transformation,[],[f2])).
% 0.92/1.07  
% 0.92/1.07  fof(f13,plain,(
% 0.92/1.07    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.92/1.07    inference(flattening,[],[f12])).
% 0.92/1.07  
% 0.92/1.07  fof(f23,plain,(
% 0.92/1.07    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.92/1.07    inference(cnf_transformation,[],[f13])).
% 0.92/1.07  
% 0.92/1.07  fof(f1,axiom,(
% 0.92/1.07    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.92/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.07  
% 0.92/1.07  fof(f10,plain,(
% 0.92/1.07    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.92/1.07    inference(ennf_transformation,[],[f1])).
% 0.92/1.07  
% 0.92/1.07  fof(f11,plain,(
% 0.92/1.07    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.92/1.07    inference(flattening,[],[f10])).
% 0.92/1.07  
% 0.92/1.07  fof(f20,plain,(
% 0.92/1.07    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.92/1.07    inference(cnf_transformation,[],[f11])).
% 0.92/1.07  
% 0.92/1.07  fof(f21,plain,(
% 0.92/1.07    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.92/1.07    inference(cnf_transformation,[],[f11])).
% 0.92/1.07  
% 0.92/1.07  fof(f22,plain,(
% 0.92/1.07    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.92/1.07    inference(cnf_transformation,[],[f11])).
% 0.92/1.07  
% 0.92/1.07  fof(f4,axiom,(
% 0.92/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.92/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.07  
% 0.92/1.07  fof(f15,plain,(
% 0.92/1.07    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/1.07    inference(ennf_transformation,[],[f4])).
% 0.92/1.07  
% 0.92/1.07  fof(f25,plain,(
% 0.92/1.07    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/1.07    inference(cnf_transformation,[],[f15])).
% 0.92/1.07  
% 0.92/1.07  fof(f5,conjecture,(
% 0.92/1.07    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 0.92/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.07  
% 0.92/1.07  fof(f6,negated_conjecture,(
% 0.92/1.07    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 0.92/1.07    inference(negated_conjecture,[],[f5])).
% 0.92/1.07  
% 0.92/1.07  fof(f7,plain,(
% 0.92/1.07    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 0.92/1.07    inference(pure_predicate_removal,[],[f6])).
% 0.92/1.07  
% 0.92/1.07  fof(f8,plain,(
% 0.92/1.07    ~! [X0] : (~v2_struct_0(X0) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 0.92/1.07    inference(pure_predicate_removal,[],[f7])).
% 0.92/1.07  
% 0.92/1.07  fof(f9,plain,(
% 0.92/1.07    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))),
% 0.92/1.07    inference(pure_predicate_removal,[],[f8])).
% 0.92/1.07  
% 0.92/1.07  fof(f16,plain,(
% 0.92/1.07    ? [X0,X1,X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))),
% 0.92/1.07    inference(ennf_transformation,[],[f9])).
% 0.92/1.07  
% 0.92/1.07  fof(f17,plain,(
% 0.92/1.07    ? [X0,X1,X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))),
% 0.92/1.08    inference(flattening,[],[f16])).
% 0.92/1.08  
% 0.92/1.08  fof(f18,plain,(
% 0.92/1.08    ? [X0,X1,X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.92/1.08    introduced(choice_axiom,[])).
% 0.92/1.08  
% 0.92/1.08  fof(f19,plain,(
% 0.92/1.08    (k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)),
% 0.92/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 0.92/1.08  
% 0.92/1.08  fof(f28,plain,(
% 0.92/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.92/1.08    inference(cnf_transformation,[],[f19])).
% 0.92/1.08  
% 0.92/1.08  fof(f29,plain,(
% 0.92/1.08    k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.92/1.08    inference(cnf_transformation,[],[f19])).
% 0.92/1.08  
% 0.92/1.08  fof(f26,plain,(
% 0.92/1.08    v1_funct_1(sK2)),
% 0.92/1.08    inference(cnf_transformation,[],[f19])).
% 0.92/1.08  
% 0.92/1.08  fof(f27,plain,(
% 0.92/1.08    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.92/1.08    inference(cnf_transformation,[],[f19])).
% 0.92/1.08  
% 0.92/1.08  cnf(c_106,plain,
% 0.92/1.08      ( ~ v1_funct_2(X0,X1,X2)
% 0.92/1.08      | v1_funct_2(X3,X4,X5)
% 0.92/1.08      | X3 != X0
% 0.92/1.08      | X4 != X1
% 0.92/1.08      | X5 != X2 ),
% 0.92/1.08      theory(equality) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_103,plain,
% 0.92/1.08      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.92/1.08      theory(equality) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_100,plain,
% 0.92/1.08      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 0.92/1.08      theory(equality) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_99,plain,
% 0.92/1.08      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 0.92/1.08      theory(equality) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_98,plain,
% 0.92/1.08      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 0.92/1.08      theory(equality) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_94,plain,( X0_2 = X0_2 ),theory(equality) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_4,plain,
% 0.92/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.92/1.08      inference(cnf_transformation,[],[f24]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_3,plain,
% 0.92/1.08      ( ~ v1_relat_1(X0)
% 0.92/1.08      | ~ v1_funct_1(X0)
% 0.92/1.08      | ~ v2_funct_1(X0)
% 0.92/1.08      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 0.92/1.08      inference(cnf_transformation,[],[f23]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_2,plain,
% 0.92/1.08      ( ~ v1_relat_1(X0)
% 0.92/1.08      | v1_relat_1(k2_funct_1(X0))
% 0.92/1.08      | ~ v1_funct_1(X0)
% 0.92/1.08      | ~ v2_funct_1(X0) ),
% 0.92/1.08      inference(cnf_transformation,[],[f20]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_1,plain,
% 0.92/1.08      ( ~ v1_relat_1(X0)
% 0.92/1.08      | ~ v1_funct_1(X0)
% 0.92/1.08      | v1_funct_1(k2_funct_1(X0))
% 0.92/1.08      | ~ v2_funct_1(X0) ),
% 0.92/1.08      inference(cnf_transformation,[],[f21]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_0,plain,
% 0.92/1.08      ( ~ v1_relat_1(X0)
% 0.92/1.08      | ~ v1_funct_1(X0)
% 0.92/1.08      | ~ v2_funct_1(X0)
% 0.92/1.08      | v2_funct_1(k2_funct_1(X0)) ),
% 0.92/1.08      inference(cnf_transformation,[],[f22]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_5,plain,
% 0.92/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.92/1.08      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.92/1.08      inference(cnf_transformation,[],[f25]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_7,negated_conjecture,
% 0.92/1.08      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 0.92/1.08      inference(cnf_transformation,[],[f28]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_152,plain,
% 0.92/1.08      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.92/1.08      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.92/1.08      | sK2 != X2 ),
% 0.92/1.08      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_153,plain,
% 0.92/1.08      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 0.92/1.08      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.92/1.08      inference(unflattening,[status(thm)],[c_152]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_189,plain,
% 0.92/1.08      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))
% 0.92/1.08      | k2_relset_1(X0_42,X1_42,sK2) = k2_relat_1(sK2) ),
% 0.92/1.08      inference(subtyping,[status(esa)],[c_153]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_230,plain,
% 0.92/1.08      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 0.92/1.08      inference(equality_resolution,[status(thm)],[c_189]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_6,negated_conjecture,
% 0.92/1.08      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.92/1.08      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.92/1.08      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.92/1.08      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 0.92/1.08      inference(cnf_transformation,[],[f29]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_9,negated_conjecture,
% 0.92/1.08      ( v1_funct_1(sK2) ),
% 0.92/1.08      inference(cnf_transformation,[],[f26]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_112,plain,
% 0.92/1.08      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.92/1.08      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.92/1.08      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.92/1.08      | k2_funct_1(sK2) != sK2 ),
% 0.92/1.08      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_8,negated_conjecture,
% 0.92/1.08      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 0.92/1.08      inference(cnf_transformation,[],[f27]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_132,plain,
% 0.92/1.08      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.92/1.08      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.92/1.08      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.92/1.08      | k2_funct_1(sK2) != sK2 ),
% 0.92/1.08      inference(resolution_lifted,[status(thm)],[c_112,c_8]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_161,plain,
% 0.92/1.08      ( u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.92/1.08      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.92/1.08      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 0.92/1.08      | k2_funct_1(sK2) != sK2 ),
% 0.92/1.08      inference(resolution_lifted,[status(thm)],[c_132,c_7]) ).
% 0.92/1.08  
% 0.92/1.08  cnf(c_188,plain,
% 0.92/1.08      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 0.92/1.08      | k2_funct_1(sK2) != sK2
% 0.92/1.08      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.92/1.08      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 0.92/1.08      inference(subtyping,[status(esa)],[c_161]) ).
% 0.92/1.08  
% 0.92/1.08  
% 0.92/1.08  % SZS output end Saturation for theBenchmark.p
% 0.92/1.08  
% 0.92/1.08  ------                               Statistics
% 0.92/1.08  
% 0.92/1.08  ------ General
% 0.92/1.08  
% 0.92/1.08  abstr_ref_over_cycles:                  0
% 0.92/1.08  abstr_ref_under_cycles:                 0
% 0.92/1.08  gc_basic_clause_elim:                   0
% 0.92/1.08  forced_gc_time:                         0
% 0.92/1.08  parsing_time:                           0.009
% 0.92/1.08  unif_index_cands_time:                  0.
% 0.92/1.08  unif_index_add_time:                    0.
% 0.92/1.08  orderings_time:                         0.
% 0.92/1.08  out_proof_time:                         0.
% 0.92/1.08  total_time:                             0.062
% 0.92/1.08  num_of_symbols:                         47
% 0.92/1.08  num_of_terms:                           441
% 0.92/1.08  
% 0.92/1.08  ------ Preprocessing
% 0.92/1.08  
% 0.92/1.08  num_of_splits:                          0
% 0.92/1.08  num_of_split_atoms:                     0
% 0.92/1.08  num_of_reused_defs:                     0
% 0.92/1.08  num_eq_ax_congr_red:                    8
% 0.92/1.08  num_of_sem_filtered_clauses:            5
% 0.92/1.08  num_of_subtypes:                        5
% 0.92/1.08  monotx_restored_types:                  0
% 0.92/1.08  sat_num_of_epr_types:                   0
% 0.92/1.08  sat_num_of_non_cyclic_types:            0
% 0.92/1.08  sat_guarded_non_collapsed_types:        0
% 0.92/1.08  num_pure_diseq_elim:                    0
% 0.92/1.08  simp_replaced_by:                       0
% 0.92/1.08  res_preprocessed:                       26
% 0.92/1.08  prep_upred:                             0
% 0.92/1.08  prep_unflattend:                        1
% 0.92/1.08  smt_new_axioms:                         0
% 0.92/1.08  pred_elim_cands:                        0
% 0.92/1.08  pred_elim:                              3
% 0.92/1.08  pred_elim_cl:                           3
% 0.92/1.08  pred_elim_cycles:                       4
% 0.92/1.08  merged_defs:                            0
% 0.92/1.08  merged_defs_ncl:                        0
% 0.92/1.08  bin_hyper_res:                          0
% 0.92/1.08  prep_cycles:                            3
% 0.92/1.08  pred_elim_time:                         0.001
% 0.92/1.08  splitting_time:                         0.
% 0.92/1.08  sem_filter_time:                        0.
% 0.92/1.08  monotx_time:                            0.
% 0.92/1.08  subtype_inf_time:                       0.
% 0.92/1.08  
% 0.92/1.08  ------ Problem properties
% 0.92/1.08  
% 0.92/1.08  clauses:                                2
% 0.92/1.08  conjectures:                            0
% 0.92/1.08  epr:                                    0
% 0.92/1.08  horn:                                   2
% 0.92/1.08  ground:                                 1
% 0.92/1.08  unary:                                  0
% 0.92/1.08  binary:                                 1
% 0.92/1.08  lits:                                   6
% 0.92/1.08  lits_eq:                                6
% 0.92/1.08  fd_pure:                                0
% 0.92/1.08  fd_pseudo:                              0
% 0.92/1.08  fd_cond:                                0
% 0.92/1.08  fd_pseudo_cond:                         0
% 0.92/1.08  ac_symbols:                             0
% 0.92/1.08  
% 0.92/1.08  ------ Propositional Solver
% 0.92/1.08  
% 0.92/1.08  prop_solver_calls:                      19
% 0.92/1.08  prop_fast_solver_calls:                 147
% 0.92/1.08  smt_solver_calls:                       0
% 0.92/1.08  smt_fast_solver_calls:                  0
% 0.92/1.08  prop_num_of_clauses:                    83
% 0.92/1.08  prop_preprocess_simplified:             538
% 0.92/1.08  prop_fo_subsumed:                       0
% 0.92/1.08  prop_solver_time:                       0.
% 0.92/1.08  smt_solver_time:                        0.
% 0.92/1.08  smt_fast_solver_time:                   0.
% 0.92/1.08  prop_fast_solver_time:                  0.
% 0.92/1.08  prop_unsat_core_time:                   0.
% 0.92/1.08  
% 0.92/1.08  ------ QBF
% 0.92/1.08  
% 0.92/1.08  qbf_q_res:                              0
% 0.92/1.08  qbf_num_tautologies:                    0
% 0.92/1.08  qbf_prep_cycles:                        0
% 0.92/1.08  
% 0.92/1.08  ------ BMC1
% 0.92/1.08  
% 0.92/1.08  bmc1_current_bound:                     -1
% 0.92/1.08  bmc1_last_solved_bound:                 -1
% 0.92/1.08  bmc1_unsat_core_size:                   -1
% 0.92/1.08  bmc1_unsat_core_parents_size:           -1
% 0.92/1.08  bmc1_merge_next_fun:                    0
% 0.92/1.08  bmc1_unsat_core_clauses_time:           0.
% 0.92/1.08  
% 0.92/1.08  ------ Instantiation
% 0.92/1.08  
% 0.92/1.08  inst_num_of_clauses:                    28
% 0.92/1.08  inst_num_in_passive:                    0
% 0.92/1.08  inst_num_in_active:                     19
% 0.92/1.08  inst_num_in_unprocessed:                9
% 0.92/1.08  inst_num_of_loops:                      20
% 0.92/1.08  inst_num_of_learning_restarts:          0
% 0.92/1.08  inst_num_moves_active_passive:          0
% 0.92/1.08  inst_lit_activity:                      0
% 0.92/1.08  inst_lit_activity_moves:                0
% 0.92/1.08  inst_num_tautologies:                   0
% 0.92/1.08  inst_num_prop_implied:                  0
% 0.92/1.08  inst_num_existing_simplified:           0
% 0.92/1.08  inst_num_eq_res_simplified:             0
% 0.92/1.08  inst_num_child_elim:                    0
% 0.92/1.08  inst_num_of_dismatching_blockings:      1
% 0.92/1.08  inst_num_of_non_proper_insts:           7
% 0.92/1.08  inst_num_of_duplicates:                 0
% 0.92/1.08  inst_inst_num_from_inst_to_res:         0
% 0.92/1.08  inst_dismatching_checking_time:         0.
% 0.92/1.08  
% 0.92/1.08  ------ Resolution
% 0.92/1.08  
% 0.92/1.08  res_num_of_clauses:                     0
% 0.92/1.08  res_num_in_passive:                     0
% 0.92/1.08  res_num_in_active:                      0
% 0.92/1.08  res_num_of_loops:                       29
% 0.92/1.08  res_forward_subset_subsumed:            1
% 0.92/1.08  res_backward_subset_subsumed:           0
% 0.92/1.08  res_forward_subsumed:                   0
% 0.92/1.08  res_backward_subsumed:                  0
% 0.92/1.08  res_forward_subsumption_resolution:     0
% 0.92/1.08  res_backward_subsumption_resolution:    0
% 0.92/1.08  res_clause_to_clause_subsumption:       2
% 0.92/1.08  res_orphan_elimination:                 0
% 0.92/1.08  res_tautology_del:                      0
% 0.92/1.08  res_num_eq_res_simplified:              0
% 0.92/1.08  res_num_sel_changes:                    0
% 0.92/1.08  res_moves_from_active_to_pass:          0
% 0.92/1.08  
% 0.92/1.08  ------ Superposition
% 0.92/1.08  
% 0.92/1.08  sup_time_total:                         0.
% 0.92/1.08  sup_time_generating:                    0.
% 0.92/1.08  sup_time_sim_full:                      0.
% 0.92/1.08  sup_time_sim_immed:                     0.
% 0.92/1.08  
% 0.92/1.08  sup_num_of_clauses:                     3
% 0.92/1.08  sup_num_in_active:                      3
% 0.92/1.08  sup_num_in_passive:                     0
% 0.92/1.08  sup_num_of_loops:                       3
% 0.92/1.08  sup_fw_superposition:                   0
% 0.92/1.08  sup_bw_superposition:                   0
% 0.92/1.08  sup_immediate_simplified:               0
% 0.92/1.08  sup_given_eliminated:                   0
% 0.92/1.08  comparisons_done:                       0
% 0.92/1.08  comparisons_avoided:                    0
% 0.92/1.08  
% 0.92/1.08  ------ Simplifications
% 0.92/1.08  
% 0.92/1.08  
% 0.92/1.08  sim_fw_subset_subsumed:                 0
% 0.92/1.08  sim_bw_subset_subsumed:                 0
% 0.92/1.08  sim_fw_subsumed:                        0
% 0.92/1.08  sim_bw_subsumed:                        0
% 0.92/1.08  sim_fw_subsumption_res:                 0
% 0.92/1.08  sim_bw_subsumption_res:                 0
% 0.92/1.08  sim_tautology_del:                      0
% 0.92/1.08  sim_eq_tautology_del:                   0
% 0.92/1.08  sim_eq_res_simp:                        0
% 0.92/1.08  sim_fw_demodulated:                     0
% 0.92/1.08  sim_bw_demodulated:                     0
% 0.92/1.08  sim_light_normalised:                   0
% 0.92/1.08  sim_joinable_taut:                      0
% 0.92/1.08  sim_joinable_simp:                      0
% 0.92/1.08  sim_ac_normalised:                      0
% 0.92/1.08  sim_smt_subsumption:                    0
% 0.92/1.08  
%------------------------------------------------------------------------------
