%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:53 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  170 (2314 expanded)
%              Number of clauses        :  124 ( 792 expanded)
%              Number of leaves         :   19 ( 625 expanded)
%              Depth                    :   24
%              Number of atoms          :  477 (12975 expanded)
%              Number of equality atoms :  263 (5389 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
          & ( k1_xboole_0 = k2_struct_0(X0)
            | k1_xboole_0 != k2_struct_0(X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0)
        & ( k1_xboole_0 = k2_struct_0(X0)
          | k1_xboole_0 != k2_struct_0(X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0)
            & ( k1_xboole_0 = k2_struct_0(X0)
              | k1_xboole_0 != k2_struct_0(sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0)
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29,f28,f27])).

fof(f46,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_562,plain,
    ( k2_zfmisc_1(X0_50,X1_50) = k2_zfmisc_1(X2_50,X3_50)
    | X0_50 != X2_50
    | X1_50 != X3_50 ),
    theory(equality)).

cnf(c_906,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(X0_50,X1_50)
    | u1_struct_0(sK1) != X1_50
    | u1_struct_0(sK0) != X0_50 ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_1373,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK1),X0_50)
    | u1_struct_0(sK1) != X0_50
    | u1_struct_0(sK0) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_1374,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0
    | u1_struct_0(sK0) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_559,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_976,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X1_50 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1320,plain,
    ( u1_struct_0(sK1) != X0_50
    | u1_struct_0(sK1) = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X0_50 ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_1321,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK0)
    | u1_struct_0(sK1) != k1_xboole_0
    | k2_struct_0(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_205,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_206,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_208,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_206,c_16,c_14])).

cnf(c_222,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | u1_struct_0(sK1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_208])).

cnf(c_223,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_543,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_223])).

cnf(c_739,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_198,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_199,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_544,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_199])).

cnf(c_760,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_739,c_544])).

cnf(c_17,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_193,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_194,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_545,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_761,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_760,c_545])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_331,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_332,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_374,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | k1_relat_1(X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_332])).

cnf(c_375,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ v4_relat_1(sK2,X0)
    | k1_relat_1(sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_537,plain,
    ( ~ v1_partfun1(sK2,X0_50)
    | ~ v4_relat_1(sK2,X0_50)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))
    | k1_relat_1(sK2) = X0_50 ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_551,plain,
    ( ~ v1_partfun1(sK2,X0_50)
    | ~ v4_relat_1(sK2,X0_50)
    | k1_relat_1(sK2) = X0_50
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_537])).

cnf(c_744,plain,
    ( k1_relat_1(sK2) = X0_50
    | v1_partfun1(sK2,X0_50) != iProver_top
    | v4_relat_1(sK2,X0_50) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_552,plain,
    ( sP2_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_537])).

cnf(c_588,plain,
    ( sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_589,plain,
    ( k1_relat_1(sK2) = X0_50
    | v1_partfun1(sK2,X0_50) != iProver_top
    | v4_relat_1(sK2,X0_50) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_550,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_537])).

cnf(c_745,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_776,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_745,c_544,c_545])).

cnf(c_893,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_776])).

cnf(c_956,plain,
    ( v4_relat_1(sK2,X0_50) != iProver_top
    | v1_partfun1(sK2,X0_50) != iProver_top
    | k1_relat_1(sK2) = X0_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_588,c_589,c_893])).

cnf(c_957,plain,
    ( k1_relat_1(sK2) = X0_50
    | v1_partfun1(sK2,X0_50) != iProver_top
    | v4_relat_1(sK2,X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_956])).

cnf(c_968,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | v4_relat_1(sK2,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_957])).

cnf(c_2,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_319,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_320,plain,
    ( v4_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_539,plain,
    ( v4_relat_1(sK2,X0_50)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_320])).

cnf(c_740,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | v4_relat_1(sK2,X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_782,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | v4_relat_1(sK2,X0_50) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_740,c_544,c_545])).

cnf(c_898,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_782])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_301,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_302,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_541,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k8_relset_1(X0_50,X1_50,sK2,X1_50) = k1_relset_1(X0_50,X1_50,sK2) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_808,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k8_relset_1(X0_50,X1_50,sK2,X1_50) = k1_relset_1(X0_50,X1_50,sK2) ),
    inference(light_normalisation,[status(thm)],[c_541,c_544,c_545])).

cnf(c_1059,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_808])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_310,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_311,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_540,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_311])).

cnf(c_798,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_540,c_544,c_545])).

cnf(c_924,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_798])).

cnf(c_1111,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1059,c_924])).

cnf(c_12,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_547,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_766,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_547,c_544,c_545])).

cnf(c_1113,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1111,c_766])).

cnf(c_1198,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_968,c_898,c_1113])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_546,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1212,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1198,c_546])).

cnf(c_1213,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1212])).

cnf(c_1306,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1213,c_1113])).

cnf(c_6,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_232,plain,
    ( v1_partfun1(X0,X1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_208])).

cnf(c_233,plain,
    ( v1_partfun1(X0,u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_343,plain,
    ( v1_partfun1(X0,u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_233])).

cnf(c_344,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_538,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_50)) ),
    inference(subtyping,[status(esa)],[c_344])).

cnf(c_549,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_538])).

cnf(c_741,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK1)) = iProver_top
    | v1_partfun1(sK2,u1_struct_0(sK0)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_769,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK1)) = iProver_top
    | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_741,c_544,c_545])).

cnf(c_1206,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
    | v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1198,c_769])).

cnf(c_1233,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1206,c_1213])).

cnf(c_1264,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1233])).

cnf(c_563,plain,
    ( X0_52 != X1_52
    | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
    theory(equality)).

cnf(c_860,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(X0_50,X1_50)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_1155,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK1),X0_50)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_50)) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1156,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_949,plain,
    ( X0_50 != X1_50
    | u1_struct_0(sK0) != X1_50
    | u1_struct_0(sK0) = X0_50 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1064,plain,
    ( X0_50 != k2_struct_0(sK0)
    | u1_struct_0(sK0) = X0_50
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_1135,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_944,plain,
    ( X0_50 != X1_50
    | u1_struct_0(sK1) != X1_50
    | u1_struct_0(sK1) = X0_50 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1006,plain,
    ( X0_50 != k2_struct_0(sK1)
    | u1_struct_0(sK1) = X0_50
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_1007,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_935,plain,
    ( X0_50 != X1_50
    | X0_50 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1_50 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1002,plain,
    ( X0_50 = u1_struct_0(sK0)
    | X0_50 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1003,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_555,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_931,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_878,plain,
    ( X0_50 != X1_50
    | k2_struct_0(sK0) != X1_50
    | k2_struct_0(sK0) = X0_50 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_930,plain,
    ( X0_50 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = X0_50
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_932,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_564,plain,
    ( ~ v4_relat_1(X0_49,X0_50)
    | v4_relat_1(X0_49,X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_900,plain,
    ( v4_relat_1(sK2,X0_50)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | X0_50 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_902,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | v4_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_894,plain,
    ( ~ sP1_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_893])).

cnf(c_862,plain,
    ( k2_struct_0(sK1) != X0_50
    | k1_xboole_0 != X0_50
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_863,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_857,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_556,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_854,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_590,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ v4_relat_1(sK2,k1_xboole_0)
    | ~ sP2_iProver_split
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_548,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_50))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_538])).

cnf(c_586,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_573,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1374,c_1321,c_1306,c_1264,c_1156,c_1135,c_1113,c_1007,c_1003,c_968,c_931,c_932,c_902,c_898,c_894,c_863,c_857,c_854,c_590,c_552,c_586,c_544,c_545,c_546,c_573])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.12/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.12/1.01  
% 1.12/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.12/1.01  
% 1.12/1.01  ------  iProver source info
% 1.12/1.01  
% 1.12/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.12/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.12/1.01  git: non_committed_changes: false
% 1.12/1.01  git: last_make_outside_of_git: false
% 1.12/1.01  
% 1.12/1.01  ------ 
% 1.12/1.01  
% 1.12/1.01  ------ Input Options
% 1.12/1.01  
% 1.12/1.01  --out_options                           all
% 1.12/1.01  --tptp_safe_out                         true
% 1.12/1.01  --problem_path                          ""
% 1.12/1.01  --include_path                          ""
% 1.12/1.01  --clausifier                            res/vclausify_rel
% 1.12/1.01  --clausifier_options                    --mode clausify
% 1.12/1.01  --stdin                                 false
% 1.12/1.01  --stats_out                             all
% 1.12/1.01  
% 1.12/1.01  ------ General Options
% 1.12/1.01  
% 1.12/1.01  --fof                                   false
% 1.12/1.01  --time_out_real                         305.
% 1.12/1.01  --time_out_virtual                      -1.
% 1.12/1.01  --symbol_type_check                     false
% 1.12/1.01  --clausify_out                          false
% 1.12/1.01  --sig_cnt_out                           false
% 1.12/1.01  --trig_cnt_out                          false
% 1.12/1.01  --trig_cnt_out_tolerance                1.
% 1.12/1.01  --trig_cnt_out_sk_spl                   false
% 1.12/1.01  --abstr_cl_out                          false
% 1.12/1.01  
% 1.12/1.01  ------ Global Options
% 1.12/1.01  
% 1.12/1.01  --schedule                              default
% 1.12/1.01  --add_important_lit                     false
% 1.12/1.01  --prop_solver_per_cl                    1000
% 1.12/1.01  --min_unsat_core                        false
% 1.12/1.01  --soft_assumptions                      false
% 1.12/1.01  --soft_lemma_size                       3
% 1.12/1.01  --prop_impl_unit_size                   0
% 1.12/1.01  --prop_impl_unit                        []
% 1.12/1.01  --share_sel_clauses                     true
% 1.12/1.01  --reset_solvers                         false
% 1.12/1.01  --bc_imp_inh                            [conj_cone]
% 1.12/1.01  --conj_cone_tolerance                   3.
% 1.12/1.01  --extra_neg_conj                        none
% 1.12/1.01  --large_theory_mode                     true
% 1.12/1.01  --prolific_symb_bound                   200
% 1.12/1.01  --lt_threshold                          2000
% 1.12/1.01  --clause_weak_htbl                      true
% 1.12/1.01  --gc_record_bc_elim                     false
% 1.12/1.01  
% 1.12/1.01  ------ Preprocessing Options
% 1.12/1.01  
% 1.12/1.01  --preprocessing_flag                    true
% 1.12/1.01  --time_out_prep_mult                    0.1
% 1.12/1.01  --splitting_mode                        input
% 1.12/1.01  --splitting_grd                         true
% 1.12/1.01  --splitting_cvd                         false
% 1.12/1.01  --splitting_cvd_svl                     false
% 1.12/1.01  --splitting_nvd                         32
% 1.12/1.01  --sub_typing                            true
% 1.12/1.01  --prep_gs_sim                           true
% 1.12/1.01  --prep_unflatten                        true
% 1.12/1.01  --prep_res_sim                          true
% 1.12/1.01  --prep_upred                            true
% 1.12/1.01  --prep_sem_filter                       exhaustive
% 1.12/1.01  --prep_sem_filter_out                   false
% 1.12/1.01  --pred_elim                             true
% 1.12/1.01  --res_sim_input                         true
% 1.12/1.01  --eq_ax_congr_red                       true
% 1.12/1.01  --pure_diseq_elim                       true
% 1.12/1.01  --brand_transform                       false
% 1.12/1.01  --non_eq_to_eq                          false
% 1.12/1.01  --prep_def_merge                        true
% 1.12/1.01  --prep_def_merge_prop_impl              false
% 1.12/1.01  --prep_def_merge_mbd                    true
% 1.12/1.01  --prep_def_merge_tr_red                 false
% 1.12/1.01  --prep_def_merge_tr_cl                  false
% 1.12/1.01  --smt_preprocessing                     true
% 1.12/1.01  --smt_ac_axioms                         fast
% 1.12/1.01  --preprocessed_out                      false
% 1.12/1.01  --preprocessed_stats                    false
% 1.12/1.01  
% 1.12/1.01  ------ Abstraction refinement Options
% 1.12/1.01  
% 1.12/1.01  --abstr_ref                             []
% 1.12/1.01  --abstr_ref_prep                        false
% 1.12/1.01  --abstr_ref_until_sat                   false
% 1.12/1.01  --abstr_ref_sig_restrict                funpre
% 1.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.12/1.01  --abstr_ref_under                       []
% 1.12/1.01  
% 1.12/1.01  ------ SAT Options
% 1.12/1.01  
% 1.12/1.01  --sat_mode                              false
% 1.12/1.01  --sat_fm_restart_options                ""
% 1.12/1.01  --sat_gr_def                            false
% 1.12/1.01  --sat_epr_types                         true
% 1.12/1.01  --sat_non_cyclic_types                  false
% 1.12/1.01  --sat_finite_models                     false
% 1.12/1.01  --sat_fm_lemmas                         false
% 1.12/1.01  --sat_fm_prep                           false
% 1.12/1.01  --sat_fm_uc_incr                        true
% 1.12/1.01  --sat_out_model                         small
% 1.12/1.01  --sat_out_clauses                       false
% 1.12/1.01  
% 1.12/1.01  ------ QBF Options
% 1.12/1.01  
% 1.12/1.01  --qbf_mode                              false
% 1.12/1.01  --qbf_elim_univ                         false
% 1.12/1.01  --qbf_dom_inst                          none
% 1.12/1.01  --qbf_dom_pre_inst                      false
% 1.12/1.01  --qbf_sk_in                             false
% 1.12/1.01  --qbf_pred_elim                         true
% 1.12/1.01  --qbf_split                             512
% 1.12/1.01  
% 1.12/1.01  ------ BMC1 Options
% 1.12/1.01  
% 1.12/1.01  --bmc1_incremental                      false
% 1.12/1.01  --bmc1_axioms                           reachable_all
% 1.12/1.01  --bmc1_min_bound                        0
% 1.12/1.01  --bmc1_max_bound                        -1
% 1.12/1.01  --bmc1_max_bound_default                -1
% 1.12/1.01  --bmc1_symbol_reachability              true
% 1.12/1.01  --bmc1_property_lemmas                  false
% 1.12/1.01  --bmc1_k_induction                      false
% 1.12/1.01  --bmc1_non_equiv_states                 false
% 1.12/1.01  --bmc1_deadlock                         false
% 1.12/1.01  --bmc1_ucm                              false
% 1.12/1.01  --bmc1_add_unsat_core                   none
% 1.12/1.01  --bmc1_unsat_core_children              false
% 1.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.12/1.01  --bmc1_out_stat                         full
% 1.12/1.01  --bmc1_ground_init                      false
% 1.12/1.01  --bmc1_pre_inst_next_state              false
% 1.12/1.01  --bmc1_pre_inst_state                   false
% 1.12/1.01  --bmc1_pre_inst_reach_state             false
% 1.12/1.01  --bmc1_out_unsat_core                   false
% 1.12/1.01  --bmc1_aig_witness_out                  false
% 1.12/1.01  --bmc1_verbose                          false
% 1.12/1.01  --bmc1_dump_clauses_tptp                false
% 1.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.12/1.01  --bmc1_dump_file                        -
% 1.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.12/1.01  --bmc1_ucm_extend_mode                  1
% 1.12/1.01  --bmc1_ucm_init_mode                    2
% 1.12/1.01  --bmc1_ucm_cone_mode                    none
% 1.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.12/1.01  --bmc1_ucm_relax_model                  4
% 1.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.12/1.01  --bmc1_ucm_layered_model                none
% 1.12/1.01  --bmc1_ucm_max_lemma_size               10
% 1.12/1.01  
% 1.12/1.01  ------ AIG Options
% 1.12/1.01  
% 1.12/1.01  --aig_mode                              false
% 1.12/1.01  
% 1.12/1.01  ------ Instantiation Options
% 1.12/1.01  
% 1.12/1.01  --instantiation_flag                    true
% 1.12/1.01  --inst_sos_flag                         false
% 1.12/1.01  --inst_sos_phase                        true
% 1.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.12/1.01  --inst_lit_sel_side                     num_symb
% 1.12/1.01  --inst_solver_per_active                1400
% 1.12/1.01  --inst_solver_calls_frac                1.
% 1.12/1.01  --inst_passive_queue_type               priority_queues
% 1.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.12/1.01  --inst_passive_queues_freq              [25;2]
% 1.12/1.01  --inst_dismatching                      true
% 1.12/1.01  --inst_eager_unprocessed_to_passive     true
% 1.12/1.01  --inst_prop_sim_given                   true
% 1.12/1.01  --inst_prop_sim_new                     false
% 1.12/1.01  --inst_subs_new                         false
% 1.12/1.01  --inst_eq_res_simp                      false
% 1.12/1.01  --inst_subs_given                       false
% 1.12/1.01  --inst_orphan_elimination               true
% 1.12/1.01  --inst_learning_loop_flag               true
% 1.12/1.01  --inst_learning_start                   3000
% 1.12/1.01  --inst_learning_factor                  2
% 1.12/1.01  --inst_start_prop_sim_after_learn       3
% 1.12/1.01  --inst_sel_renew                        solver
% 1.12/1.01  --inst_lit_activity_flag                true
% 1.12/1.01  --inst_restr_to_given                   false
% 1.12/1.01  --inst_activity_threshold               500
% 1.12/1.01  --inst_out_proof                        true
% 1.12/1.01  
% 1.12/1.01  ------ Resolution Options
% 1.12/1.01  
% 1.12/1.01  --resolution_flag                       true
% 1.12/1.01  --res_lit_sel                           adaptive
% 1.12/1.01  --res_lit_sel_side                      none
% 1.12/1.01  --res_ordering                          kbo
% 1.12/1.01  --res_to_prop_solver                    active
% 1.12/1.01  --res_prop_simpl_new                    false
% 1.12/1.01  --res_prop_simpl_given                  true
% 1.12/1.01  --res_passive_queue_type                priority_queues
% 1.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.12/1.01  --res_passive_queues_freq               [15;5]
% 1.12/1.01  --res_forward_subs                      full
% 1.12/1.01  --res_backward_subs                     full
% 1.12/1.01  --res_forward_subs_resolution           true
% 1.12/1.01  --res_backward_subs_resolution          true
% 1.12/1.01  --res_orphan_elimination                true
% 1.12/1.01  --res_time_limit                        2.
% 1.12/1.01  --res_out_proof                         true
% 1.12/1.01  
% 1.12/1.01  ------ Superposition Options
% 1.12/1.01  
% 1.12/1.01  --superposition_flag                    true
% 1.12/1.01  --sup_passive_queue_type                priority_queues
% 1.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.12/1.01  --demod_completeness_check              fast
% 1.12/1.01  --demod_use_ground                      true
% 1.12/1.01  --sup_to_prop_solver                    passive
% 1.12/1.01  --sup_prop_simpl_new                    true
% 1.12/1.01  --sup_prop_simpl_given                  true
% 1.12/1.01  --sup_fun_splitting                     false
% 1.12/1.01  --sup_smt_interval                      50000
% 1.12/1.01  
% 1.12/1.01  ------ Superposition Simplification Setup
% 1.12/1.01  
% 1.12/1.01  --sup_indices_passive                   []
% 1.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.12/1.01  --sup_full_bw                           [BwDemod]
% 1.12/1.01  --sup_immed_triv                        [TrivRules]
% 1.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.12/1.01  --sup_immed_bw_main                     []
% 1.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.12/1.01  
% 1.12/1.01  ------ Combination Options
% 1.12/1.01  
% 1.12/1.01  --comb_res_mult                         3
% 1.12/1.01  --comb_sup_mult                         2
% 1.12/1.01  --comb_inst_mult                        10
% 1.12/1.01  
% 1.12/1.01  ------ Debug Options
% 1.12/1.01  
% 1.12/1.01  --dbg_backtrace                         false
% 1.12/1.01  --dbg_dump_prop_clauses                 false
% 1.12/1.01  --dbg_dump_prop_clauses_file            -
% 1.12/1.01  --dbg_out_stat                          false
% 1.12/1.01  ------ Parsing...
% 1.12/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.12/1.01  
% 1.12/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.12/1.01  
% 1.12/1.01  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.12/1.01  
% 1.12/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.12/1.01  ------ Proving...
% 1.12/1.01  ------ Problem Properties 
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  clauses                                 16
% 1.12/1.01  conjectures                             2
% 1.12/1.01  EPR                                     1
% 1.12/1.01  Horn                                    12
% 1.12/1.01  unary                                   3
% 1.12/1.01  binary                                  10
% 1.12/1.01  lits                                    33
% 1.12/1.01  lits eq                                 17
% 1.12/1.01  fd_pure                                 0
% 1.12/1.01  fd_pseudo                               0
% 1.12/1.01  fd_cond                                 1
% 1.12/1.01  fd_pseudo_cond                          0
% 1.12/1.01  AC symbols                              0
% 1.12/1.01  
% 1.12/1.01  ------ Schedule dynamic 5 is on 
% 1.12/1.01  
% 1.12/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  ------ 
% 1.12/1.01  Current options:
% 1.12/1.01  ------ 
% 1.12/1.01  
% 1.12/1.01  ------ Input Options
% 1.12/1.01  
% 1.12/1.01  --out_options                           all
% 1.12/1.01  --tptp_safe_out                         true
% 1.12/1.01  --problem_path                          ""
% 1.12/1.01  --include_path                          ""
% 1.12/1.01  --clausifier                            res/vclausify_rel
% 1.12/1.01  --clausifier_options                    --mode clausify
% 1.12/1.01  --stdin                                 false
% 1.12/1.01  --stats_out                             all
% 1.12/1.01  
% 1.12/1.01  ------ General Options
% 1.12/1.01  
% 1.12/1.01  --fof                                   false
% 1.12/1.01  --time_out_real                         305.
% 1.12/1.01  --time_out_virtual                      -1.
% 1.12/1.01  --symbol_type_check                     false
% 1.12/1.01  --clausify_out                          false
% 1.12/1.01  --sig_cnt_out                           false
% 1.12/1.01  --trig_cnt_out                          false
% 1.12/1.01  --trig_cnt_out_tolerance                1.
% 1.12/1.01  --trig_cnt_out_sk_spl                   false
% 1.12/1.01  --abstr_cl_out                          false
% 1.12/1.01  
% 1.12/1.01  ------ Global Options
% 1.12/1.01  
% 1.12/1.01  --schedule                              default
% 1.12/1.01  --add_important_lit                     false
% 1.12/1.01  --prop_solver_per_cl                    1000
% 1.12/1.01  --min_unsat_core                        false
% 1.12/1.01  --soft_assumptions                      false
% 1.12/1.01  --soft_lemma_size                       3
% 1.12/1.01  --prop_impl_unit_size                   0
% 1.12/1.01  --prop_impl_unit                        []
% 1.12/1.01  --share_sel_clauses                     true
% 1.12/1.01  --reset_solvers                         false
% 1.12/1.01  --bc_imp_inh                            [conj_cone]
% 1.12/1.01  --conj_cone_tolerance                   3.
% 1.12/1.01  --extra_neg_conj                        none
% 1.12/1.01  --large_theory_mode                     true
% 1.12/1.01  --prolific_symb_bound                   200
% 1.12/1.01  --lt_threshold                          2000
% 1.12/1.01  --clause_weak_htbl                      true
% 1.12/1.01  --gc_record_bc_elim                     false
% 1.12/1.01  
% 1.12/1.01  ------ Preprocessing Options
% 1.12/1.01  
% 1.12/1.01  --preprocessing_flag                    true
% 1.12/1.01  --time_out_prep_mult                    0.1
% 1.12/1.01  --splitting_mode                        input
% 1.12/1.01  --splitting_grd                         true
% 1.12/1.01  --splitting_cvd                         false
% 1.12/1.01  --splitting_cvd_svl                     false
% 1.12/1.01  --splitting_nvd                         32
% 1.12/1.01  --sub_typing                            true
% 1.12/1.01  --prep_gs_sim                           true
% 1.12/1.01  --prep_unflatten                        true
% 1.12/1.01  --prep_res_sim                          true
% 1.12/1.01  --prep_upred                            true
% 1.12/1.01  --prep_sem_filter                       exhaustive
% 1.12/1.01  --prep_sem_filter_out                   false
% 1.12/1.01  --pred_elim                             true
% 1.12/1.01  --res_sim_input                         true
% 1.12/1.01  --eq_ax_congr_red                       true
% 1.12/1.01  --pure_diseq_elim                       true
% 1.12/1.01  --brand_transform                       false
% 1.12/1.01  --non_eq_to_eq                          false
% 1.12/1.01  --prep_def_merge                        true
% 1.12/1.01  --prep_def_merge_prop_impl              false
% 1.12/1.01  --prep_def_merge_mbd                    true
% 1.12/1.01  --prep_def_merge_tr_red                 false
% 1.12/1.01  --prep_def_merge_tr_cl                  false
% 1.12/1.01  --smt_preprocessing                     true
% 1.12/1.01  --smt_ac_axioms                         fast
% 1.12/1.01  --preprocessed_out                      false
% 1.12/1.01  --preprocessed_stats                    false
% 1.12/1.01  
% 1.12/1.01  ------ Abstraction refinement Options
% 1.12/1.01  
% 1.12/1.01  --abstr_ref                             []
% 1.12/1.01  --abstr_ref_prep                        false
% 1.12/1.01  --abstr_ref_until_sat                   false
% 1.12/1.01  --abstr_ref_sig_restrict                funpre
% 1.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.12/1.01  --abstr_ref_under                       []
% 1.12/1.01  
% 1.12/1.01  ------ SAT Options
% 1.12/1.01  
% 1.12/1.01  --sat_mode                              false
% 1.12/1.01  --sat_fm_restart_options                ""
% 1.12/1.01  --sat_gr_def                            false
% 1.12/1.01  --sat_epr_types                         true
% 1.12/1.01  --sat_non_cyclic_types                  false
% 1.12/1.01  --sat_finite_models                     false
% 1.12/1.01  --sat_fm_lemmas                         false
% 1.12/1.01  --sat_fm_prep                           false
% 1.12/1.01  --sat_fm_uc_incr                        true
% 1.12/1.01  --sat_out_model                         small
% 1.12/1.01  --sat_out_clauses                       false
% 1.12/1.01  
% 1.12/1.01  ------ QBF Options
% 1.12/1.01  
% 1.12/1.01  --qbf_mode                              false
% 1.12/1.01  --qbf_elim_univ                         false
% 1.12/1.01  --qbf_dom_inst                          none
% 1.12/1.01  --qbf_dom_pre_inst                      false
% 1.12/1.01  --qbf_sk_in                             false
% 1.12/1.01  --qbf_pred_elim                         true
% 1.12/1.01  --qbf_split                             512
% 1.12/1.01  
% 1.12/1.01  ------ BMC1 Options
% 1.12/1.01  
% 1.12/1.01  --bmc1_incremental                      false
% 1.12/1.01  --bmc1_axioms                           reachable_all
% 1.12/1.01  --bmc1_min_bound                        0
% 1.12/1.01  --bmc1_max_bound                        -1
% 1.12/1.01  --bmc1_max_bound_default                -1
% 1.12/1.01  --bmc1_symbol_reachability              true
% 1.12/1.01  --bmc1_property_lemmas                  false
% 1.12/1.01  --bmc1_k_induction                      false
% 1.12/1.01  --bmc1_non_equiv_states                 false
% 1.12/1.01  --bmc1_deadlock                         false
% 1.12/1.01  --bmc1_ucm                              false
% 1.12/1.01  --bmc1_add_unsat_core                   none
% 1.12/1.01  --bmc1_unsat_core_children              false
% 1.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.12/1.01  --bmc1_out_stat                         full
% 1.12/1.01  --bmc1_ground_init                      false
% 1.12/1.01  --bmc1_pre_inst_next_state              false
% 1.12/1.01  --bmc1_pre_inst_state                   false
% 1.12/1.01  --bmc1_pre_inst_reach_state             false
% 1.12/1.01  --bmc1_out_unsat_core                   false
% 1.12/1.01  --bmc1_aig_witness_out                  false
% 1.12/1.01  --bmc1_verbose                          false
% 1.12/1.01  --bmc1_dump_clauses_tptp                false
% 1.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.12/1.01  --bmc1_dump_file                        -
% 1.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.12/1.01  --bmc1_ucm_extend_mode                  1
% 1.12/1.01  --bmc1_ucm_init_mode                    2
% 1.12/1.01  --bmc1_ucm_cone_mode                    none
% 1.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.12/1.01  --bmc1_ucm_relax_model                  4
% 1.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.12/1.01  --bmc1_ucm_layered_model                none
% 1.12/1.01  --bmc1_ucm_max_lemma_size               10
% 1.12/1.01  
% 1.12/1.01  ------ AIG Options
% 1.12/1.01  
% 1.12/1.01  --aig_mode                              false
% 1.12/1.01  
% 1.12/1.01  ------ Instantiation Options
% 1.12/1.01  
% 1.12/1.01  --instantiation_flag                    true
% 1.12/1.01  --inst_sos_flag                         false
% 1.12/1.01  --inst_sos_phase                        true
% 1.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.12/1.01  --inst_lit_sel_side                     none
% 1.12/1.01  --inst_solver_per_active                1400
% 1.12/1.01  --inst_solver_calls_frac                1.
% 1.12/1.01  --inst_passive_queue_type               priority_queues
% 1.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.12/1.01  --inst_passive_queues_freq              [25;2]
% 1.12/1.01  --inst_dismatching                      true
% 1.12/1.01  --inst_eager_unprocessed_to_passive     true
% 1.12/1.01  --inst_prop_sim_given                   true
% 1.12/1.01  --inst_prop_sim_new                     false
% 1.12/1.01  --inst_subs_new                         false
% 1.12/1.01  --inst_eq_res_simp                      false
% 1.12/1.01  --inst_subs_given                       false
% 1.12/1.01  --inst_orphan_elimination               true
% 1.12/1.01  --inst_learning_loop_flag               true
% 1.12/1.01  --inst_learning_start                   3000
% 1.12/1.01  --inst_learning_factor                  2
% 1.12/1.01  --inst_start_prop_sim_after_learn       3
% 1.12/1.01  --inst_sel_renew                        solver
% 1.12/1.01  --inst_lit_activity_flag                true
% 1.12/1.01  --inst_restr_to_given                   false
% 1.12/1.01  --inst_activity_threshold               500
% 1.12/1.01  --inst_out_proof                        true
% 1.12/1.01  
% 1.12/1.01  ------ Resolution Options
% 1.12/1.01  
% 1.12/1.01  --resolution_flag                       false
% 1.12/1.01  --res_lit_sel                           adaptive
% 1.12/1.01  --res_lit_sel_side                      none
% 1.12/1.01  --res_ordering                          kbo
% 1.12/1.01  --res_to_prop_solver                    active
% 1.12/1.01  --res_prop_simpl_new                    false
% 1.12/1.01  --res_prop_simpl_given                  true
% 1.12/1.01  --res_passive_queue_type                priority_queues
% 1.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.12/1.01  --res_passive_queues_freq               [15;5]
% 1.12/1.01  --res_forward_subs                      full
% 1.12/1.01  --res_backward_subs                     full
% 1.12/1.01  --res_forward_subs_resolution           true
% 1.12/1.01  --res_backward_subs_resolution          true
% 1.12/1.01  --res_orphan_elimination                true
% 1.12/1.01  --res_time_limit                        2.
% 1.12/1.01  --res_out_proof                         true
% 1.12/1.01  
% 1.12/1.01  ------ Superposition Options
% 1.12/1.01  
% 1.12/1.01  --superposition_flag                    true
% 1.12/1.01  --sup_passive_queue_type                priority_queues
% 1.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.12/1.01  --demod_completeness_check              fast
% 1.12/1.01  --demod_use_ground                      true
% 1.12/1.01  --sup_to_prop_solver                    passive
% 1.12/1.01  --sup_prop_simpl_new                    true
% 1.12/1.01  --sup_prop_simpl_given                  true
% 1.12/1.01  --sup_fun_splitting                     false
% 1.12/1.01  --sup_smt_interval                      50000
% 1.12/1.01  
% 1.12/1.01  ------ Superposition Simplification Setup
% 1.12/1.01  
% 1.12/1.01  --sup_indices_passive                   []
% 1.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.12/1.01  --sup_full_bw                           [BwDemod]
% 1.12/1.01  --sup_immed_triv                        [TrivRules]
% 1.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.12/1.01  --sup_immed_bw_main                     []
% 1.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.12/1.01  
% 1.12/1.01  ------ Combination Options
% 1.12/1.01  
% 1.12/1.01  --comb_res_mult                         3
% 1.12/1.01  --comb_sup_mult                         2
% 1.12/1.01  --comb_inst_mult                        10
% 1.12/1.01  
% 1.12/1.01  ------ Debug Options
% 1.12/1.01  
% 1.12/1.01  --dbg_backtrace                         false
% 1.12/1.01  --dbg_dump_prop_clauses                 false
% 1.12/1.01  --dbg_dump_prop_clauses_file            -
% 1.12/1.01  --dbg_out_stat                          false
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  ------ Proving...
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  % SZS status Theorem for theBenchmark.p
% 1.12/1.01  
% 1.12/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.12/1.01  
% 1.12/1.01  fof(f1,axiom,(
% 1.12/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f13,plain,(
% 1.12/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.12/1.01    inference(ennf_transformation,[],[f1])).
% 1.12/1.01  
% 1.12/1.01  fof(f31,plain,(
% 1.12/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.12/1.01    inference(cnf_transformation,[],[f13])).
% 1.12/1.01  
% 1.12/1.01  fof(f7,axiom,(
% 1.12/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f19,plain,(
% 1.12/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.12/1.01    inference(ennf_transformation,[],[f7])).
% 1.12/1.01  
% 1.12/1.01  fof(f20,plain,(
% 1.12/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.12/1.01    inference(flattening,[],[f19])).
% 1.12/1.01  
% 1.12/1.01  fof(f39,plain,(
% 1.12/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.12/1.01    inference(cnf_transformation,[],[f20])).
% 1.12/1.01  
% 1.12/1.01  fof(f10,conjecture,(
% 1.12/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f11,negated_conjecture,(
% 1.12/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.12/1.01    inference(negated_conjecture,[],[f10])).
% 1.12/1.01  
% 1.12/1.01  fof(f24,plain,(
% 1.12/1.01    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.12/1.01    inference(ennf_transformation,[],[f11])).
% 1.12/1.01  
% 1.12/1.01  fof(f25,plain,(
% 1.12/1.01    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.12/1.01    inference(flattening,[],[f24])).
% 1.12/1.01  
% 1.12/1.01  fof(f29,plain,(
% 1.12/1.01    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.12/1.01    introduced(choice_axiom,[])).
% 1.12/1.01  
% 1.12/1.01  fof(f28,plain,(
% 1.12/1.01    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 1.12/1.01    introduced(choice_axiom,[])).
% 1.12/1.01  
% 1.12/1.01  fof(f27,plain,(
% 1.12/1.01    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 1.12/1.01    introduced(choice_axiom,[])).
% 1.12/1.01  
% 1.12/1.01  fof(f30,plain,(
% 1.12/1.01    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29,f28,f27])).
% 1.12/1.01  
% 1.12/1.01  fof(f46,plain,(
% 1.12/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.12/1.01    inference(cnf_transformation,[],[f30])).
% 1.12/1.01  
% 1.12/1.01  fof(f45,plain,(
% 1.12/1.01    v1_funct_1(sK2)),
% 1.12/1.01    inference(cnf_transformation,[],[f30])).
% 1.12/1.01  
% 1.12/1.01  fof(f47,plain,(
% 1.12/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.12/1.01    inference(cnf_transformation,[],[f30])).
% 1.12/1.01  
% 1.12/1.01  fof(f9,axiom,(
% 1.12/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f23,plain,(
% 1.12/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.12/1.01    inference(ennf_transformation,[],[f9])).
% 1.12/1.01  
% 1.12/1.01  fof(f42,plain,(
% 1.12/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.12/1.01    inference(cnf_transformation,[],[f23])).
% 1.12/1.01  
% 1.12/1.01  fof(f43,plain,(
% 1.12/1.01    l1_struct_0(sK0)),
% 1.12/1.01    inference(cnf_transformation,[],[f30])).
% 1.12/1.01  
% 1.12/1.01  fof(f44,plain,(
% 1.12/1.01    l1_struct_0(sK1)),
% 1.12/1.01    inference(cnf_transformation,[],[f30])).
% 1.12/1.01  
% 1.12/1.01  fof(f8,axiom,(
% 1.12/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f21,plain,(
% 1.12/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.12/1.01    inference(ennf_transformation,[],[f8])).
% 1.12/1.01  
% 1.12/1.01  fof(f22,plain,(
% 1.12/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.12/1.01    inference(flattening,[],[f21])).
% 1.12/1.01  
% 1.12/1.01  fof(f26,plain,(
% 1.12/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.12/1.01    inference(nnf_transformation,[],[f22])).
% 1.12/1.01  
% 1.12/1.01  fof(f40,plain,(
% 1.12/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.12/1.01    inference(cnf_transformation,[],[f26])).
% 1.12/1.01  
% 1.12/1.01  fof(f2,axiom,(
% 1.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f14,plain,(
% 1.12/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.12/1.01    inference(ennf_transformation,[],[f2])).
% 1.12/1.01  
% 1.12/1.01  fof(f32,plain,(
% 1.12/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.12/1.01    inference(cnf_transformation,[],[f14])).
% 1.12/1.01  
% 1.12/1.01  fof(f3,axiom,(
% 1.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f12,plain,(
% 1.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.12/1.01    inference(pure_predicate_removal,[],[f3])).
% 1.12/1.01  
% 1.12/1.01  fof(f15,plain,(
% 1.12/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.12/1.01    inference(ennf_transformation,[],[f12])).
% 1.12/1.01  
% 1.12/1.01  fof(f33,plain,(
% 1.12/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.12/1.01    inference(cnf_transformation,[],[f15])).
% 1.12/1.01  
% 1.12/1.01  fof(f5,axiom,(
% 1.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f17,plain,(
% 1.12/1.01    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.12/1.01    inference(ennf_transformation,[],[f5])).
% 1.12/1.01  
% 1.12/1.01  fof(f36,plain,(
% 1.12/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.12/1.01    inference(cnf_transformation,[],[f17])).
% 1.12/1.01  
% 1.12/1.01  fof(f4,axiom,(
% 1.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f16,plain,(
% 1.12/1.01    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.12/1.01    inference(ennf_transformation,[],[f4])).
% 1.12/1.01  
% 1.12/1.01  fof(f34,plain,(
% 1.12/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.12/1.01    inference(cnf_transformation,[],[f16])).
% 1.12/1.01  
% 1.12/1.01  fof(f49,plain,(
% 1.12/1.01    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 1.12/1.01    inference(cnf_transformation,[],[f30])).
% 1.12/1.01  
% 1.12/1.01  fof(f48,plain,(
% 1.12/1.01    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 1.12/1.01    inference(cnf_transformation,[],[f30])).
% 1.12/1.01  
% 1.12/1.01  fof(f6,axiom,(
% 1.12/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.12/1.01  
% 1.12/1.01  fof(f18,plain,(
% 1.12/1.01    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.12/1.01    inference(ennf_transformation,[],[f6])).
% 1.12/1.01  
% 1.12/1.01  fof(f37,plain,(
% 1.12/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.12/1.01    inference(cnf_transformation,[],[f18])).
% 1.12/1.01  
% 1.12/1.01  cnf(c_562,plain,
% 1.12/1.01      ( k2_zfmisc_1(X0_50,X1_50) = k2_zfmisc_1(X2_50,X3_50)
% 1.12/1.01      | X0_50 != X2_50
% 1.12/1.01      | X1_50 != X3_50 ),
% 1.12/1.01      theory(equality) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_906,plain,
% 1.12/1.01      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(X0_50,X1_50)
% 1.12/1.01      | u1_struct_0(sK1) != X1_50
% 1.12/1.01      | u1_struct_0(sK0) != X0_50 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_562]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1373,plain,
% 1.12/1.01      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK1),X0_50)
% 1.12/1.01      | u1_struct_0(sK1) != X0_50
% 1.12/1.01      | u1_struct_0(sK0) != u1_struct_0(sK1) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_906]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1374,plain,
% 1.12/1.01      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)
% 1.12/1.01      | u1_struct_0(sK1) != k1_xboole_0
% 1.12/1.01      | u1_struct_0(sK0) != u1_struct_0(sK1) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_1373]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_559,plain,
% 1.12/1.01      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 1.12/1.01      theory(equality) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_976,plain,
% 1.12/1.01      ( X0_50 != X1_50
% 1.12/1.01      | X0_50 = k2_struct_0(sK0)
% 1.12/1.01      | k2_struct_0(sK0) != X1_50 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_559]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1320,plain,
% 1.12/1.01      ( u1_struct_0(sK1) != X0_50
% 1.12/1.01      | u1_struct_0(sK1) = k2_struct_0(sK0)
% 1.12/1.01      | k2_struct_0(sK0) != X0_50 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_976]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1321,plain,
% 1.12/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK0)
% 1.12/1.01      | u1_struct_0(sK1) != k1_xboole_0
% 1.12/1.01      | k2_struct_0(sK0) != k1_xboole_0 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_1320]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_0,plain,
% 1.12/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.12/1.01      inference(cnf_transformation,[],[f31]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_7,plain,
% 1.12/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.12/1.01      | v1_partfun1(X0,X1)
% 1.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.12/1.01      | ~ v1_funct_1(X0)
% 1.12/1.01      | v1_xboole_0(X2) ),
% 1.12/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_15,negated_conjecture,
% 1.12/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.12/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_205,plain,
% 1.12/1.01      ( v1_partfun1(X0,X1)
% 1.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.12/1.01      | ~ v1_funct_1(X0)
% 1.12/1.01      | v1_xboole_0(X2)
% 1.12/1.01      | u1_struct_0(sK1) != X2
% 1.12/1.01      | u1_struct_0(sK0) != X1
% 1.12/1.01      | sK2 != X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_206,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.12/1.01      | ~ v1_funct_1(sK2)
% 1.12/1.01      | v1_xboole_0(u1_struct_0(sK1)) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_205]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_16,negated_conjecture,
% 1.12/1.01      ( v1_funct_1(sK2) ),
% 1.12/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_14,negated_conjecture,
% 1.12/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.12/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_208,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | v1_xboole_0(u1_struct_0(sK1)) ),
% 1.12/1.01      inference(global_propositional_subsumption,
% 1.12/1.01                [status(thm)],
% 1.12/1.01                [c_206,c_16,c_14]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_222,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | u1_struct_0(sK1) != X0
% 1.12/1.01      | k1_xboole_0 = X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_208]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_223,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_222]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_543,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_223]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_739,plain,
% 1.12/1.01      ( k1_xboole_0 = u1_struct_0(sK1)
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 1.12/1.01      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_11,plain,
% 1.12/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.12/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_18,negated_conjecture,
% 1.12/1.01      ( l1_struct_0(sK0) ),
% 1.12/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_198,plain,
% 1.12/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_199,plain,
% 1.12/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_198]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_544,plain,
% 1.12/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_199]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_760,plain,
% 1.12/1.01      ( u1_struct_0(sK1) = k1_xboole_0
% 1.12/1.01      | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_739,c_544]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_17,negated_conjecture,
% 1.12/1.01      ( l1_struct_0(sK1) ),
% 1.12/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_193,plain,
% 1.12/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_194,plain,
% 1.12/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_193]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_545,plain,
% 1.12/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_194]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_761,plain,
% 1.12/1.01      ( k2_struct_0(sK1) = k1_xboole_0
% 1.12/1.01      | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 1.12/1.01      inference(demodulation,[status(thm)],[c_760,c_545]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_10,plain,
% 1.12/1.01      ( ~ v1_partfun1(X0,X1)
% 1.12/1.01      | ~ v4_relat_1(X0,X1)
% 1.12/1.01      | ~ v1_relat_1(X0)
% 1.12/1.01      | k1_relat_1(X0) = X1 ),
% 1.12/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1,plain,
% 1.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.12/1.01      | v1_relat_1(X0) ),
% 1.12/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_331,plain,
% 1.12/1.01      ( v1_relat_1(X0)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.12/1.01      | sK2 != X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_332,plain,
% 1.12/1.01      ( v1_relat_1(sK2)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_331]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_374,plain,
% 1.12/1.01      ( ~ v1_partfun1(X0,X1)
% 1.12/1.01      | ~ v4_relat_1(X0,X1)
% 1.12/1.01      | k1_relat_1(X0) = X1
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 1.12/1.01      | sK2 != X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_332]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_375,plain,
% 1.12/1.01      ( ~ v1_partfun1(sK2,X0)
% 1.12/1.01      | ~ v4_relat_1(sK2,X0)
% 1.12/1.01      | k1_relat_1(sK2) = X0
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_374]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_537,plain,
% 1.12/1.01      ( ~ v1_partfun1(sK2,X0_50)
% 1.12/1.01      | ~ v4_relat_1(sK2,X0_50)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))
% 1.12/1.01      | k1_relat_1(sK2) = X0_50 ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_375]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_551,plain,
% 1.12/1.01      ( ~ v1_partfun1(sK2,X0_50)
% 1.12/1.01      | ~ v4_relat_1(sK2,X0_50)
% 1.12/1.01      | k1_relat_1(sK2) = X0_50
% 1.12/1.01      | ~ sP2_iProver_split ),
% 1.12/1.01      inference(splitting,
% 1.12/1.01                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 1.12/1.01                [c_537]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_744,plain,
% 1.12/1.01      ( k1_relat_1(sK2) = X0_50
% 1.12/1.01      | v1_partfun1(sK2,X0_50) != iProver_top
% 1.12/1.01      | v4_relat_1(sK2,X0_50) != iProver_top
% 1.12/1.01      | sP2_iProver_split != iProver_top ),
% 1.12/1.01      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_552,plain,
% 1.12/1.01      ( sP2_iProver_split | sP1_iProver_split ),
% 1.12/1.01      inference(splitting,
% 1.12/1.01                [splitting(split),new_symbols(definition,[])],
% 1.12/1.01                [c_537]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_588,plain,
% 1.12/1.01      ( sP2_iProver_split = iProver_top
% 1.12/1.01      | sP1_iProver_split = iProver_top ),
% 1.12/1.01      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_589,plain,
% 1.12/1.01      ( k1_relat_1(sK2) = X0_50
% 1.12/1.01      | v1_partfun1(sK2,X0_50) != iProver_top
% 1.12/1.01      | v4_relat_1(sK2,X0_50) != iProver_top
% 1.12/1.01      | sP2_iProver_split != iProver_top ),
% 1.12/1.01      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_550,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | ~ sP1_iProver_split ),
% 1.12/1.01      inference(splitting,
% 1.12/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.12/1.01                [c_537]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_745,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | sP1_iProver_split != iProver_top ),
% 1.12/1.01      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_776,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | sP1_iProver_split != iProver_top ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_745,c_544,c_545]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_893,plain,
% 1.12/1.01      ( sP1_iProver_split != iProver_top ),
% 1.12/1.01      inference(equality_resolution,[status(thm)],[c_776]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_956,plain,
% 1.12/1.01      ( v4_relat_1(sK2,X0_50) != iProver_top
% 1.12/1.01      | v1_partfun1(sK2,X0_50) != iProver_top
% 1.12/1.01      | k1_relat_1(sK2) = X0_50 ),
% 1.12/1.01      inference(global_propositional_subsumption,
% 1.12/1.01                [status(thm)],
% 1.12/1.01                [c_744,c_588,c_589,c_893]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_957,plain,
% 1.12/1.01      ( k1_relat_1(sK2) = X0_50
% 1.12/1.01      | v1_partfun1(sK2,X0_50) != iProver_top
% 1.12/1.01      | v4_relat_1(sK2,X0_50) != iProver_top ),
% 1.12/1.01      inference(renaming,[status(thm)],[c_956]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_968,plain,
% 1.12/1.01      ( k2_struct_0(sK1) = k1_xboole_0
% 1.12/1.01      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.12/1.01      | v4_relat_1(sK2,k2_struct_0(sK0)) != iProver_top ),
% 1.12/1.01      inference(superposition,[status(thm)],[c_761,c_957]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_2,plain,
% 1.12/1.01      ( v4_relat_1(X0,X1)
% 1.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.12/1.01      inference(cnf_transformation,[],[f33]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_319,plain,
% 1.12/1.01      ( v4_relat_1(X0,X1)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.12/1.01      | sK2 != X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_14]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_320,plain,
% 1.12/1.01      ( v4_relat_1(sK2,X0)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_319]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_539,plain,
% 1.12/1.01      ( v4_relat_1(sK2,X0_50)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_320]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_740,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | v4_relat_1(sK2,X0_50) = iProver_top ),
% 1.12/1.01      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_782,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | v4_relat_1(sK2,X0_50) = iProver_top ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_740,c_544,c_545]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_898,plain,
% 1.12/1.01      ( v4_relat_1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 1.12/1.01      inference(equality_resolution,[status(thm)],[c_782]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_4,plain,
% 1.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.12/1.01      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 1.12/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_301,plain,
% 1.12/1.01      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.12/1.01      | sK2 != X2 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_302,plain,
% 1.12/1.01      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_301]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_541,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | k8_relset_1(X0_50,X1_50,sK2,X1_50) = k1_relset_1(X0_50,X1_50,sK2) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_302]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_808,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | k8_relset_1(X0_50,X1_50,sK2,X1_50) = k1_relset_1(X0_50,X1_50,sK2) ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_541,c_544,c_545]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1059,plain,
% 1.12/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 1.12/1.01      inference(equality_resolution,[status(thm)],[c_808]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_3,plain,
% 1.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.12/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.12/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_310,plain,
% 1.12/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.12/1.01      | sK2 != X2 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_311,plain,
% 1.12/1.01      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_310]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_540,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_311]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_798,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.12/1.01      | k1_relset_1(X0_50,X1_50,sK2) = k1_relat_1(sK2) ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_540,c_544,c_545]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_924,plain,
% 1.12/1.01      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 1.12/1.01      inference(equality_resolution,[status(thm)],[c_798]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1111,plain,
% 1.12/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_1059,c_924]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_12,negated_conjecture,
% 1.12/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 1.12/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_547,negated_conjecture,
% 1.12/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_766,plain,
% 1.12/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_547,c_544,c_545]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1113,plain,
% 1.12/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 1.12/1.01      inference(demodulation,[status(thm)],[c_1111,c_766]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1198,plain,
% 1.12/1.01      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 1.12/1.01      inference(global_propositional_subsumption,
% 1.12/1.01                [status(thm)],
% 1.12/1.01                [c_968,c_898,c_1113]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_13,negated_conjecture,
% 1.12/1.01      ( k1_xboole_0 != k2_struct_0(sK1)
% 1.12/1.01      | k1_xboole_0 = k2_struct_0(sK0) ),
% 1.12/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_546,negated_conjecture,
% 1.12/1.01      ( k1_xboole_0 != k2_struct_0(sK1)
% 1.12/1.01      | k1_xboole_0 = k2_struct_0(sK0) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1212,plain,
% 1.12/1.01      ( k2_struct_0(sK0) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.12/1.01      inference(demodulation,[status(thm)],[c_1198,c_546]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1213,plain,
% 1.12/1.01      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 1.12/1.01      inference(equality_resolution_simp,[status(thm)],[c_1212]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1306,plain,
% 1.12/1.01      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 1.12/1.01      inference(demodulation,[status(thm)],[c_1213,c_1113]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_6,plain,
% 1.12/1.01      ( v1_partfun1(X0,X1)
% 1.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.12/1.01      | ~ v1_xboole_0(X1) ),
% 1.12/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_232,plain,
% 1.12/1.01      ( v1_partfun1(X0,X1)
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.12/1.01      | u1_struct_0(sK1) != X1 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_208]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_233,plain,
% 1.12/1.01      ( v1_partfun1(X0,u1_struct_0(sK1))
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_232]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_343,plain,
% 1.12/1.01      ( v1_partfun1(X0,u1_struct_0(sK1))
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))
% 1.12/1.01      | sK2 != X0 ),
% 1.12/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_233]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_344,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK1))
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)) ),
% 1.12/1.01      inference(unflattening,[status(thm)],[c_343]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_538,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK1))
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_50)) ),
% 1.12/1.01      inference(subtyping,[status(esa)],[c_344]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_549,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK1))
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | sP0_iProver_split ),
% 1.12/1.01      inference(splitting,
% 1.12/1.01                [splitting(split),new_symbols(definition,[])],
% 1.12/1.01                [c_538]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_741,plain,
% 1.12/1.01      ( v1_partfun1(sK2,u1_struct_0(sK1)) = iProver_top
% 1.12/1.01      | v1_partfun1(sK2,u1_struct_0(sK0)) = iProver_top
% 1.12/1.01      | sP0_iProver_split = iProver_top ),
% 1.12/1.01      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_769,plain,
% 1.12/1.01      ( v1_partfun1(sK2,k2_struct_0(sK1)) = iProver_top
% 1.12/1.01      | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
% 1.12/1.01      | sP0_iProver_split = iProver_top ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_741,c_544,c_545]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1206,plain,
% 1.12/1.01      ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
% 1.12/1.01      | v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 1.12/1.01      | sP0_iProver_split = iProver_top ),
% 1.12/1.01      inference(demodulation,[status(thm)],[c_1198,c_769]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1233,plain,
% 1.12/1.01      ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 1.12/1.01      | sP0_iProver_split = iProver_top ),
% 1.12/1.01      inference(light_normalisation,[status(thm)],[c_1206,c_1213]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1264,plain,
% 1.12/1.01      ( v1_partfun1(sK2,k1_xboole_0) | sP0_iProver_split ),
% 1.12/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1233]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_563,plain,
% 1.12/1.01      ( X0_52 != X1_52 | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
% 1.12/1.01      theory(equality) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_860,plain,
% 1.12/1.01      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(X0_50,X1_50)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_563]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1155,plain,
% 1.12/1.01      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK1),X0_50)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_50)) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_860]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1156,plain,
% 1.12/1.01      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_1155]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_949,plain,
% 1.12/1.01      ( X0_50 != X1_50
% 1.12/1.01      | u1_struct_0(sK0) != X1_50
% 1.12/1.01      | u1_struct_0(sK0) = X0_50 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_559]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1064,plain,
% 1.12/1.01      ( X0_50 != k2_struct_0(sK0)
% 1.12/1.01      | u1_struct_0(sK0) = X0_50
% 1.12/1.01      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_949]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1135,plain,
% 1.12/1.01      ( u1_struct_0(sK1) != k2_struct_0(sK0)
% 1.12/1.01      | u1_struct_0(sK0) = u1_struct_0(sK1)
% 1.12/1.01      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_1064]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_944,plain,
% 1.12/1.01      ( X0_50 != X1_50
% 1.12/1.01      | u1_struct_0(sK1) != X1_50
% 1.12/1.01      | u1_struct_0(sK1) = X0_50 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_559]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1006,plain,
% 1.12/1.01      ( X0_50 != k2_struct_0(sK1)
% 1.12/1.01      | u1_struct_0(sK1) = X0_50
% 1.12/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_944]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1007,plain,
% 1.12/1.01      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 1.12/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 1.12/1.01      | k1_xboole_0 != k2_struct_0(sK1) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_1006]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_935,plain,
% 1.12/1.01      ( X0_50 != X1_50
% 1.12/1.01      | X0_50 = u1_struct_0(sK0)
% 1.12/1.01      | u1_struct_0(sK0) != X1_50 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_559]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1002,plain,
% 1.12/1.01      ( X0_50 = u1_struct_0(sK0)
% 1.12/1.01      | X0_50 != k2_struct_0(sK0)
% 1.12/1.01      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_935]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_1003,plain,
% 1.12/1.01      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 1.12/1.01      | k1_xboole_0 = u1_struct_0(sK0)
% 1.12/1.01      | k1_xboole_0 != k2_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_1002]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_555,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_931,plain,
% 1.12/1.01      ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_555]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_878,plain,
% 1.12/1.01      ( X0_50 != X1_50
% 1.12/1.01      | k2_struct_0(sK0) != X1_50
% 1.12/1.01      | k2_struct_0(sK0) = X0_50 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_559]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_930,plain,
% 1.12/1.01      ( X0_50 != k2_struct_0(sK0)
% 1.12/1.01      | k2_struct_0(sK0) = X0_50
% 1.12/1.01      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_878]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_932,plain,
% 1.12/1.01      ( k2_struct_0(sK0) != k2_struct_0(sK0)
% 1.12/1.01      | k2_struct_0(sK0) = k1_xboole_0
% 1.12/1.01      | k1_xboole_0 != k2_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_930]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_564,plain,
% 1.12/1.01      ( ~ v4_relat_1(X0_49,X0_50)
% 1.12/1.01      | v4_relat_1(X0_49,X1_50)
% 1.12/1.01      | X1_50 != X0_50 ),
% 1.12/1.01      theory(equality) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_900,plain,
% 1.12/1.01      ( v4_relat_1(sK2,X0_50)
% 1.12/1.01      | ~ v4_relat_1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | X0_50 != u1_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_564]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_902,plain,
% 1.12/1.01      ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | v4_relat_1(sK2,k1_xboole_0)
% 1.12/1.01      | k1_xboole_0 != u1_struct_0(sK0) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_900]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_894,plain,
% 1.12/1.01      ( ~ sP1_iProver_split ),
% 1.12/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_893]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_862,plain,
% 1.12/1.01      ( k2_struct_0(sK1) != X0_50
% 1.12/1.01      | k1_xboole_0 != X0_50
% 1.12/1.01      | k1_xboole_0 = k2_struct_0(sK1) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_559]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_863,plain,
% 1.12/1.01      ( k2_struct_0(sK1) != k1_xboole_0
% 1.12/1.01      | k1_xboole_0 = k2_struct_0(sK1)
% 1.12/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_862]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_857,plain,
% 1.12/1.01      ( v4_relat_1(sK2,u1_struct_0(sK0))
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_539]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_556,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_854,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_556]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_590,plain,
% 1.12/1.01      ( ~ v1_partfun1(sK2,k1_xboole_0)
% 1.12/1.01      | ~ v4_relat_1(sK2,k1_xboole_0)
% 1.12/1.01      | ~ sP2_iProver_split
% 1.12/1.01      | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_551]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_548,plain,
% 1.12/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_50))
% 1.12/1.01      | ~ sP0_iProver_split ),
% 1.12/1.01      inference(splitting,
% 1.12/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.12/1.01                [c_538]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_586,plain,
% 1.12/1.01      ( ~ sP0_iProver_split
% 1.12/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_548]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(c_573,plain,
% 1.12/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 1.12/1.01      inference(instantiation,[status(thm)],[c_555]) ).
% 1.12/1.01  
% 1.12/1.01  cnf(contradiction,plain,
% 1.12/1.01      ( $false ),
% 1.12/1.01      inference(minisat,
% 1.12/1.01                [status(thm)],
% 1.12/1.01                [c_1374,c_1321,c_1306,c_1264,c_1156,c_1135,c_1113,c_1007,
% 1.12/1.01                 c_1003,c_968,c_931,c_932,c_902,c_898,c_894,c_863,c_857,
% 1.12/1.01                 c_854,c_590,c_552,c_586,c_544,c_545,c_546,c_573]) ).
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.12/1.01  
% 1.12/1.01  ------                               Statistics
% 1.12/1.01  
% 1.12/1.01  ------ General
% 1.12/1.01  
% 1.12/1.01  abstr_ref_over_cycles:                  0
% 1.12/1.01  abstr_ref_under_cycles:                 0
% 1.12/1.01  gc_basic_clause_elim:                   0
% 1.12/1.01  forced_gc_time:                         0
% 1.12/1.01  parsing_time:                           0.011
% 1.12/1.01  unif_index_cands_time:                  0.
% 1.12/1.01  unif_index_add_time:                    0.
% 1.12/1.01  orderings_time:                         0.
% 1.12/1.01  out_proof_time:                         0.015
% 1.12/1.01  total_time:                             0.081
% 1.12/1.01  num_of_symbols:                         58
% 1.12/1.01  num_of_terms:                           1196
% 1.12/1.01  
% 1.12/1.01  ------ Preprocessing
% 1.12/1.01  
% 1.12/1.01  num_of_splits:                          4
% 1.12/1.01  num_of_split_atoms:                     3
% 1.12/1.01  num_of_reused_defs:                     1
% 1.12/1.01  num_eq_ax_congr_red:                    38
% 1.12/1.01  num_of_sem_filtered_clauses:            4
% 1.12/1.01  num_of_subtypes:                        6
% 1.12/1.01  monotx_restored_types:                  0
% 1.12/1.01  sat_num_of_epr_types:                   0
% 1.12/1.01  sat_num_of_non_cyclic_types:            0
% 1.12/1.01  sat_guarded_non_collapsed_types:        1
% 1.12/1.01  num_pure_diseq_elim:                    0
% 1.12/1.01  simp_replaced_by:                       0
% 1.12/1.01  res_preprocessed:                       82
% 1.12/1.01  prep_upred:                             0
% 1.12/1.01  prep_unflattend:                        17
% 1.12/1.01  smt_new_axioms:                         0
% 1.12/1.01  pred_elim_cands:                        2
% 1.12/1.01  pred_elim:                              6
% 1.12/1.01  pred_elim_cl:                           6
% 1.12/1.01  pred_elim_cycles:                       9
% 1.12/1.01  merged_defs:                            0
% 1.12/1.01  merged_defs_ncl:                        0
% 1.12/1.01  bin_hyper_res:                          0
% 1.12/1.01  prep_cycles:                            4
% 1.12/1.01  pred_elim_time:                         0.005
% 1.12/1.01  splitting_time:                         0.
% 1.12/1.01  sem_filter_time:                        0.
% 1.12/1.01  monotx_time:                            0.
% 1.12/1.01  subtype_inf_time:                       0.
% 1.12/1.01  
% 1.12/1.01  ------ Problem properties
% 1.12/1.01  
% 1.12/1.01  clauses:                                16
% 1.12/1.01  conjectures:                            2
% 1.12/1.01  epr:                                    1
% 1.12/1.01  horn:                                   12
% 1.12/1.01  ground:                                 8
% 1.12/1.01  unary:                                  3
% 1.12/1.01  binary:                                 10
% 1.12/1.01  lits:                                   33
% 1.12/1.01  lits_eq:                                17
% 1.12/1.01  fd_pure:                                0
% 1.12/1.01  fd_pseudo:                              0
% 1.12/1.01  fd_cond:                                1
% 1.12/1.01  fd_pseudo_cond:                         0
% 1.12/1.01  ac_symbols:                             0
% 1.12/1.01  
% 1.12/1.01  ------ Propositional Solver
% 1.12/1.01  
% 1.12/1.01  prop_solver_calls:                      28
% 1.12/1.01  prop_fast_solver_calls:                 458
% 1.12/1.01  smt_solver_calls:                       0
% 1.12/1.01  smt_fast_solver_calls:                  0
% 1.12/1.01  prop_num_of_clauses:                    429
% 1.12/1.01  prop_preprocess_simplified:             1942
% 1.12/1.01  prop_fo_subsumed:                       7
% 1.12/1.01  prop_solver_time:                       0.
% 1.12/1.01  smt_solver_time:                        0.
% 1.12/1.01  smt_fast_solver_time:                   0.
% 1.12/1.01  prop_fast_solver_time:                  0.
% 1.12/1.01  prop_unsat_core_time:                   0.
% 1.12/1.01  
% 1.12/1.01  ------ QBF
% 1.12/1.01  
% 1.12/1.01  qbf_q_res:                              0
% 1.12/1.01  qbf_num_tautologies:                    0
% 1.12/1.01  qbf_prep_cycles:                        0
% 1.12/1.01  
% 1.12/1.01  ------ BMC1
% 1.12/1.01  
% 1.12/1.01  bmc1_current_bound:                     -1
% 1.12/1.01  bmc1_last_solved_bound:                 -1
% 1.12/1.01  bmc1_unsat_core_size:                   -1
% 1.12/1.01  bmc1_unsat_core_parents_size:           -1
% 1.12/1.01  bmc1_merge_next_fun:                    0
% 1.12/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.12/1.01  
% 1.12/1.01  ------ Instantiation
% 1.12/1.01  
% 1.12/1.01  inst_num_of_clauses:                    140
% 1.12/1.01  inst_num_in_passive:                    13
% 1.12/1.01  inst_num_in_active:                     94
% 1.12/1.01  inst_num_in_unprocessed:                32
% 1.12/1.01  inst_num_of_loops:                      132
% 1.12/1.01  inst_num_of_learning_restarts:          0
% 1.12/1.01  inst_num_moves_active_passive:          33
% 1.12/1.01  inst_lit_activity:                      0
% 1.12/1.01  inst_lit_activity_moves:                0
% 1.12/1.01  inst_num_tautologies:                   0
% 1.12/1.01  inst_num_prop_implied:                  0
% 1.12/1.01  inst_num_existing_simplified:           0
% 1.12/1.01  inst_num_eq_res_simplified:             0
% 1.12/1.01  inst_num_child_elim:                    0
% 1.12/1.01  inst_num_of_dismatching_blockings:      32
% 1.12/1.01  inst_num_of_non_proper_insts:           132
% 1.12/1.01  inst_num_of_duplicates:                 0
% 1.12/1.01  inst_inst_num_from_inst_to_res:         0
% 1.12/1.01  inst_dismatching_checking_time:         0.
% 1.12/1.01  
% 1.12/1.01  ------ Resolution
% 1.12/1.01  
% 1.12/1.01  res_num_of_clauses:                     0
% 1.12/1.01  res_num_in_passive:                     0
% 1.12/1.01  res_num_in_active:                      0
% 1.12/1.01  res_num_of_loops:                       86
% 1.12/1.01  res_forward_subset_subsumed:            35
% 1.12/1.01  res_backward_subset_subsumed:           0
% 1.12/1.01  res_forward_subsumed:                   0
% 1.12/1.01  res_backward_subsumed:                  0
% 1.12/1.01  res_forward_subsumption_resolution:     0
% 1.12/1.01  res_backward_subsumption_resolution:    0
% 1.12/1.01  res_clause_to_clause_subsumption:       33
% 1.12/1.01  res_orphan_elimination:                 0
% 1.12/1.01  res_tautology_del:                      13
% 1.12/1.01  res_num_eq_res_simplified:              0
% 1.12/1.01  res_num_sel_changes:                    0
% 1.12/1.01  res_moves_from_active_to_pass:          0
% 1.12/1.01  
% 1.12/1.01  ------ Superposition
% 1.12/1.01  
% 1.12/1.01  sup_time_total:                         0.
% 1.12/1.01  sup_time_generating:                    0.
% 1.12/1.01  sup_time_sim_full:                      0.
% 1.12/1.01  sup_time_sim_immed:                     0.
% 1.12/1.01  
% 1.12/1.01  sup_num_of_clauses:                     20
% 1.12/1.01  sup_num_in_active:                      9
% 1.12/1.01  sup_num_in_passive:                     11
% 1.12/1.01  sup_num_of_loops:                       26
% 1.12/1.01  sup_fw_superposition:                   0
% 1.12/1.01  sup_bw_superposition:                   2
% 1.12/1.01  sup_immediate_simplified:               10
% 1.12/1.01  sup_given_eliminated:                   0
% 1.12/1.01  comparisons_done:                       0
% 1.12/1.01  comparisons_avoided:                    0
% 1.12/1.01  
% 1.12/1.01  ------ Simplifications
% 1.12/1.01  
% 1.12/1.01  
% 1.12/1.01  sim_fw_subset_subsumed:                 1
% 1.12/1.01  sim_bw_subset_subsumed:                 1
% 1.12/1.01  sim_fw_subsumed:                        0
% 1.12/1.01  sim_bw_subsumed:                        0
% 1.12/1.01  sim_fw_subsumption_res:                 0
% 1.12/1.01  sim_bw_subsumption_res:                 0
% 1.12/1.01  sim_tautology_del:                      0
% 1.12/1.01  sim_eq_tautology_del:                   0
% 1.12/1.01  sim_eq_res_simp:                        1
% 1.12/1.01  sim_fw_demodulated:                     1
% 1.12/1.01  sim_bw_demodulated:                     16
% 1.12/1.01  sim_light_normalised:                   20
% 1.12/1.01  sim_joinable_taut:                      0
% 1.12/1.01  sim_joinable_simp:                      0
% 1.12/1.01  sim_ac_normalised:                      0
% 1.12/1.01  sim_smt_subsumption:                    0
% 1.12/1.01  
%------------------------------------------------------------------------------
