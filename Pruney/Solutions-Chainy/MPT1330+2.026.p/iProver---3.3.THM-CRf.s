%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:58 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  150 (6211 expanded)
%              Number of clauses        :  105 (2000 expanded)
%              Number of leaves         :   13 (1725 expanded)
%              Depth                    :   28
%              Number of atoms          :  461 (37472 expanded)
%              Number of equality atoms :  250 (15369 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f27,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25,f24])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f37])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_299,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_300,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_496,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k8_relset_1(X0_49,X1_49,sK2,X1_49) = k1_relset_1(X0_49,X1_49,sK2) ),
    inference(subtyping,[status(esa)],[c_300])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_191,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_192,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_499,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_192])).

cnf(c_16,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_186,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_187,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_500,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_700,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k8_relset_1(X0_49,X1_49,sK2,X1_49) = k1_relset_1(X0_49,X1_49,sK2) ),
    inference(light_normalisation,[status(thm)],[c_496,c_499,c_500])).

cnf(c_1049,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_700])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_254,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_255,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_257,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_15,c_13])).

cnf(c_7,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_317,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_318,plain,
    ( v4_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_362,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_relat_1(X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_318])).

cnf(c_363,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_425,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) != X0
    | k1_relat_1(sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_363])).

cnf(c_426,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_493,plain,
    ( ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_49))
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_426])).

cnf(c_507,plain,
    ( ~ v1_relat_1(sK2)
    | sP1_iProver_split
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_493])).

cnf(c_649,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | v1_relat_1(sK2) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_679,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_649,c_499,c_500])).

cnf(c_511,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_744,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_506,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_49))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_493])).

cnf(c_650,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_49))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_669,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_49))
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_650,c_499,c_500])).

cnf(c_778,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_669])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_275,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_276,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_498,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_276])).

cnf(c_739,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_784,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_785,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_503,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_806,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_807,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_861,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_744,c_778,c_785,c_807])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_501,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_870,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_861,c_501])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_290,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_291,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_497,plain,
    ( k7_relset_1(X0_49,X1_49,sK2,X0_49) = k2_relset_1(X0_49,X1_49,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_695,plain,
    ( k7_relset_1(X0_49,X1_49,sK2,X0_49) = k2_relset_1(X0_49,X1_49,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(light_normalisation,[status(thm)],[c_497,c_499,c_500])).

cnf(c_1028,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_695])).

cnf(c_1432,plain,
    ( k7_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k1_relat_1(sK2)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_870,c_1028])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_308,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_309,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_495,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_674,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_495,c_499,c_500])).

cnf(c_916,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_870,c_674])).

cnf(c_1113,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_916])).

cnf(c_1047,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k8_relset_1(X0_49,X1_49,sK2,X1_49) = k1_relset_1(X0_49,X1_49,sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_870,c_700])).

cnf(c_1155,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1047])).

cnf(c_11,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_502,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_661,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_502,c_499,c_500])).

cnf(c_920,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_870,c_661])).

cnf(c_1343,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1155,c_920])).

cnf(c_1350,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1113,c_1343])).

cnf(c_1441,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1432,c_870,c_1350])).

cnf(c_1549,plain,
    ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_1049,c_1441])).

cnf(c_1461,plain,
    ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1441,c_661])).

cnf(c_1551,plain,
    ( k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1549,c_1461])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_237,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_238,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_240,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | v1_partfun1(sK2,k1_xboole_0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_238,c_15])).

cnf(c_241,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_329,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_241])).

cnf(c_404,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_363])).

cnf(c_405,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_494,plain,
    ( ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_505,plain,
    ( ~ v1_relat_1(sK2)
    | sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_494])).

cnf(c_647,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_705,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_647,c_499,c_500])).

cnf(c_504,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_494])).

cnf(c_648,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_664,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_648,c_499,c_500])).

cnf(c_711,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_705,c_664])).

cnf(c_1231,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k2_struct_0(sK0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_711,c_744,c_785,c_807])).

cnf(c_1232,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1231])).

cnf(c_1446,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1441,c_1232])).

cnf(c_1494,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1446])).

cnf(c_824,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_674])).

cnf(c_1447,plain,
    ( k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1441,c_824])).

cnf(c_1496,plain,
    ( k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1494,c_1447])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1551,c_1496])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.51/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.51/1.04  
% 0.51/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.51/1.04  
% 0.51/1.04  ------  iProver source info
% 0.51/1.04  
% 0.51/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.51/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.51/1.04  git: non_committed_changes: false
% 0.51/1.04  git: last_make_outside_of_git: false
% 0.51/1.04  
% 0.51/1.04  ------ 
% 0.51/1.04  
% 0.51/1.04  ------ Input Options
% 0.51/1.04  
% 0.51/1.04  --out_options                           all
% 0.51/1.04  --tptp_safe_out                         true
% 0.51/1.04  --problem_path                          ""
% 0.51/1.04  --include_path                          ""
% 0.51/1.04  --clausifier                            res/vclausify_rel
% 0.51/1.04  --clausifier_options                    --mode clausify
% 0.51/1.04  --stdin                                 false
% 0.51/1.04  --stats_out                             all
% 0.51/1.04  
% 0.51/1.04  ------ General Options
% 0.51/1.04  
% 0.51/1.04  --fof                                   false
% 0.51/1.04  --time_out_real                         305.
% 0.51/1.04  --time_out_virtual                      -1.
% 0.51/1.04  --symbol_type_check                     false
% 0.51/1.04  --clausify_out                          false
% 0.51/1.04  --sig_cnt_out                           false
% 0.51/1.04  --trig_cnt_out                          false
% 0.51/1.04  --trig_cnt_out_tolerance                1.
% 0.51/1.04  --trig_cnt_out_sk_spl                   false
% 0.51/1.04  --abstr_cl_out                          false
% 0.51/1.04  
% 0.51/1.04  ------ Global Options
% 0.51/1.04  
% 0.51/1.04  --schedule                              default
% 0.51/1.04  --add_important_lit                     false
% 0.51/1.04  --prop_solver_per_cl                    1000
% 0.51/1.04  --min_unsat_core                        false
% 0.51/1.04  --soft_assumptions                      false
% 0.51/1.04  --soft_lemma_size                       3
% 0.51/1.04  --prop_impl_unit_size                   0
% 0.51/1.04  --prop_impl_unit                        []
% 0.51/1.04  --share_sel_clauses                     true
% 0.51/1.04  --reset_solvers                         false
% 0.51/1.04  --bc_imp_inh                            [conj_cone]
% 0.51/1.04  --conj_cone_tolerance                   3.
% 0.51/1.04  --extra_neg_conj                        none
% 0.51/1.04  --large_theory_mode                     true
% 0.51/1.04  --prolific_symb_bound                   200
% 0.51/1.04  --lt_threshold                          2000
% 0.51/1.04  --clause_weak_htbl                      true
% 0.51/1.04  --gc_record_bc_elim                     false
% 0.51/1.04  
% 0.51/1.04  ------ Preprocessing Options
% 0.51/1.04  
% 0.51/1.04  --preprocessing_flag                    true
% 0.51/1.04  --time_out_prep_mult                    0.1
% 0.51/1.04  --splitting_mode                        input
% 0.51/1.04  --splitting_grd                         true
% 0.51/1.04  --splitting_cvd                         false
% 0.51/1.04  --splitting_cvd_svl                     false
% 0.51/1.04  --splitting_nvd                         32
% 0.51/1.04  --sub_typing                            true
% 0.51/1.04  --prep_gs_sim                           true
% 0.51/1.04  --prep_unflatten                        true
% 0.51/1.04  --prep_res_sim                          true
% 0.51/1.04  --prep_upred                            true
% 0.51/1.04  --prep_sem_filter                       exhaustive
% 0.51/1.04  --prep_sem_filter_out                   false
% 0.51/1.04  --pred_elim                             true
% 0.51/1.04  --res_sim_input                         true
% 0.51/1.04  --eq_ax_congr_red                       true
% 0.51/1.04  --pure_diseq_elim                       true
% 0.51/1.04  --brand_transform                       false
% 0.51/1.04  --non_eq_to_eq                          false
% 0.51/1.04  --prep_def_merge                        true
% 0.51/1.04  --prep_def_merge_prop_impl              false
% 0.51/1.04  --prep_def_merge_mbd                    true
% 0.51/1.04  --prep_def_merge_tr_red                 false
% 0.51/1.04  --prep_def_merge_tr_cl                  false
% 0.51/1.04  --smt_preprocessing                     true
% 0.51/1.04  --smt_ac_axioms                         fast
% 0.51/1.04  --preprocessed_out                      false
% 0.51/1.04  --preprocessed_stats                    false
% 0.51/1.04  
% 0.51/1.04  ------ Abstraction refinement Options
% 0.51/1.04  
% 0.51/1.04  --abstr_ref                             []
% 0.51/1.04  --abstr_ref_prep                        false
% 0.51/1.04  --abstr_ref_until_sat                   false
% 0.51/1.04  --abstr_ref_sig_restrict                funpre
% 0.51/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.51/1.04  --abstr_ref_under                       []
% 0.51/1.04  
% 0.51/1.04  ------ SAT Options
% 0.51/1.04  
% 0.51/1.04  --sat_mode                              false
% 0.51/1.04  --sat_fm_restart_options                ""
% 0.51/1.04  --sat_gr_def                            false
% 0.51/1.04  --sat_epr_types                         true
% 0.51/1.04  --sat_non_cyclic_types                  false
% 0.51/1.04  --sat_finite_models                     false
% 0.51/1.04  --sat_fm_lemmas                         false
% 0.51/1.04  --sat_fm_prep                           false
% 0.51/1.04  --sat_fm_uc_incr                        true
% 0.51/1.04  --sat_out_model                         small
% 0.51/1.04  --sat_out_clauses                       false
% 0.51/1.04  
% 0.51/1.04  ------ QBF Options
% 0.51/1.04  
% 0.51/1.04  --qbf_mode                              false
% 0.51/1.04  --qbf_elim_univ                         false
% 0.51/1.04  --qbf_dom_inst                          none
% 0.51/1.04  --qbf_dom_pre_inst                      false
% 0.51/1.04  --qbf_sk_in                             false
% 0.51/1.04  --qbf_pred_elim                         true
% 0.51/1.04  --qbf_split                             512
% 0.51/1.04  
% 0.51/1.04  ------ BMC1 Options
% 0.51/1.04  
% 0.51/1.04  --bmc1_incremental                      false
% 0.51/1.04  --bmc1_axioms                           reachable_all
% 0.51/1.04  --bmc1_min_bound                        0
% 0.51/1.04  --bmc1_max_bound                        -1
% 0.51/1.04  --bmc1_max_bound_default                -1
% 0.51/1.04  --bmc1_symbol_reachability              true
% 0.51/1.04  --bmc1_property_lemmas                  false
% 0.51/1.04  --bmc1_k_induction                      false
% 0.51/1.04  --bmc1_non_equiv_states                 false
% 0.51/1.04  --bmc1_deadlock                         false
% 0.51/1.04  --bmc1_ucm                              false
% 0.51/1.04  --bmc1_add_unsat_core                   none
% 0.51/1.04  --bmc1_unsat_core_children              false
% 0.51/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.51/1.04  --bmc1_out_stat                         full
% 0.51/1.04  --bmc1_ground_init                      false
% 0.51/1.04  --bmc1_pre_inst_next_state              false
% 0.51/1.04  --bmc1_pre_inst_state                   false
% 0.51/1.04  --bmc1_pre_inst_reach_state             false
% 0.51/1.04  --bmc1_out_unsat_core                   false
% 0.51/1.04  --bmc1_aig_witness_out                  false
% 0.51/1.04  --bmc1_verbose                          false
% 0.51/1.04  --bmc1_dump_clauses_tptp                false
% 0.51/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.51/1.04  --bmc1_dump_file                        -
% 0.51/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.51/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.51/1.04  --bmc1_ucm_extend_mode                  1
% 0.51/1.04  --bmc1_ucm_init_mode                    2
% 0.51/1.04  --bmc1_ucm_cone_mode                    none
% 0.51/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.51/1.04  --bmc1_ucm_relax_model                  4
% 0.51/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.51/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.51/1.04  --bmc1_ucm_layered_model                none
% 0.51/1.04  --bmc1_ucm_max_lemma_size               10
% 0.51/1.04  
% 0.51/1.04  ------ AIG Options
% 0.51/1.04  
% 0.51/1.04  --aig_mode                              false
% 0.51/1.04  
% 0.51/1.04  ------ Instantiation Options
% 0.51/1.04  
% 0.51/1.04  --instantiation_flag                    true
% 0.51/1.04  --inst_sos_flag                         false
% 0.51/1.04  --inst_sos_phase                        true
% 0.51/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.51/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.51/1.04  --inst_lit_sel_side                     num_symb
% 0.51/1.04  --inst_solver_per_active                1400
% 0.51/1.04  --inst_solver_calls_frac                1.
% 0.51/1.04  --inst_passive_queue_type               priority_queues
% 0.51/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.51/1.04  --inst_passive_queues_freq              [25;2]
% 0.51/1.04  --inst_dismatching                      true
% 0.51/1.04  --inst_eager_unprocessed_to_passive     true
% 0.51/1.04  --inst_prop_sim_given                   true
% 0.51/1.04  --inst_prop_sim_new                     false
% 0.51/1.04  --inst_subs_new                         false
% 0.51/1.04  --inst_eq_res_simp                      false
% 0.51/1.04  --inst_subs_given                       false
% 0.51/1.04  --inst_orphan_elimination               true
% 0.51/1.04  --inst_learning_loop_flag               true
% 0.51/1.04  --inst_learning_start                   3000
% 0.51/1.04  --inst_learning_factor                  2
% 0.51/1.04  --inst_start_prop_sim_after_learn       3
% 0.51/1.04  --inst_sel_renew                        solver
% 0.51/1.04  --inst_lit_activity_flag                true
% 0.51/1.04  --inst_restr_to_given                   false
% 0.51/1.04  --inst_activity_threshold               500
% 0.51/1.04  --inst_out_proof                        true
% 0.51/1.04  
% 0.51/1.04  ------ Resolution Options
% 0.51/1.04  
% 0.51/1.04  --resolution_flag                       true
% 0.51/1.04  --res_lit_sel                           adaptive
% 0.51/1.04  --res_lit_sel_side                      none
% 0.51/1.04  --res_ordering                          kbo
% 0.51/1.04  --res_to_prop_solver                    active
% 0.51/1.04  --res_prop_simpl_new                    false
% 0.51/1.04  --res_prop_simpl_given                  true
% 0.51/1.04  --res_passive_queue_type                priority_queues
% 0.51/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.51/1.04  --res_passive_queues_freq               [15;5]
% 0.51/1.04  --res_forward_subs                      full
% 0.51/1.04  --res_backward_subs                     full
% 0.51/1.04  --res_forward_subs_resolution           true
% 0.51/1.04  --res_backward_subs_resolution          true
% 0.51/1.04  --res_orphan_elimination                true
% 0.51/1.04  --res_time_limit                        2.
% 0.51/1.04  --res_out_proof                         true
% 0.51/1.04  
% 0.51/1.04  ------ Superposition Options
% 0.51/1.04  
% 0.51/1.04  --superposition_flag                    true
% 0.51/1.04  --sup_passive_queue_type                priority_queues
% 0.51/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.51/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.51/1.04  --demod_completeness_check              fast
% 0.51/1.04  --demod_use_ground                      true
% 0.51/1.04  --sup_to_prop_solver                    passive
% 0.51/1.04  --sup_prop_simpl_new                    true
% 0.51/1.04  --sup_prop_simpl_given                  true
% 0.51/1.04  --sup_fun_splitting                     false
% 0.51/1.04  --sup_smt_interval                      50000
% 0.51/1.04  
% 0.51/1.04  ------ Superposition Simplification Setup
% 0.51/1.04  
% 0.51/1.04  --sup_indices_passive                   []
% 0.51/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.51/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.04  --sup_full_bw                           [BwDemod]
% 0.51/1.04  --sup_immed_triv                        [TrivRules]
% 0.51/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.51/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.04  --sup_immed_bw_main                     []
% 0.51/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.51/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.04  
% 0.51/1.04  ------ Combination Options
% 0.51/1.04  
% 0.51/1.04  --comb_res_mult                         3
% 0.51/1.04  --comb_sup_mult                         2
% 0.51/1.04  --comb_inst_mult                        10
% 0.51/1.04  
% 0.51/1.04  ------ Debug Options
% 0.51/1.04  
% 0.51/1.04  --dbg_backtrace                         false
% 0.51/1.04  --dbg_dump_prop_clauses                 false
% 0.51/1.04  --dbg_dump_prop_clauses_file            -
% 0.51/1.04  --dbg_out_stat                          false
% 0.51/1.04  ------ Parsing...
% 0.51/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.51/1.04  
% 0.51/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.51/1.04  
% 0.51/1.04  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.51/1.04  
% 0.51/1.04  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.51/1.04  ------ Proving...
% 0.51/1.04  ------ Problem Properties 
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  clauses                                 13
% 0.51/1.04  conjectures                             2
% 0.51/1.04  EPR                                     0
% 0.51/1.04  Horn                                    11
% 0.51/1.04  unary                                   4
% 0.51/1.04  binary                                  6
% 0.51/1.04  lits                                    28
% 0.51/1.04  lits eq                                 19
% 0.51/1.04  fd_pure                                 0
% 0.51/1.04  fd_pseudo                               0
% 0.51/1.04  fd_cond                                 0
% 0.51/1.04  fd_pseudo_cond                          0
% 0.51/1.04  AC symbols                              0
% 0.51/1.04  
% 0.51/1.04  ------ Schedule dynamic 5 is on 
% 0.51/1.04  
% 0.51/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  ------ 
% 0.51/1.04  Current options:
% 0.51/1.04  ------ 
% 0.51/1.04  
% 0.51/1.04  ------ Input Options
% 0.51/1.04  
% 0.51/1.04  --out_options                           all
% 0.51/1.04  --tptp_safe_out                         true
% 0.51/1.04  --problem_path                          ""
% 0.51/1.04  --include_path                          ""
% 0.51/1.04  --clausifier                            res/vclausify_rel
% 0.51/1.04  --clausifier_options                    --mode clausify
% 0.51/1.04  --stdin                                 false
% 0.51/1.04  --stats_out                             all
% 0.51/1.04  
% 0.51/1.04  ------ General Options
% 0.51/1.04  
% 0.51/1.04  --fof                                   false
% 0.51/1.04  --time_out_real                         305.
% 0.51/1.04  --time_out_virtual                      -1.
% 0.51/1.04  --symbol_type_check                     false
% 0.51/1.04  --clausify_out                          false
% 0.51/1.04  --sig_cnt_out                           false
% 0.51/1.04  --trig_cnt_out                          false
% 0.51/1.04  --trig_cnt_out_tolerance                1.
% 0.51/1.04  --trig_cnt_out_sk_spl                   false
% 0.51/1.04  --abstr_cl_out                          false
% 0.51/1.04  
% 0.51/1.04  ------ Global Options
% 0.51/1.04  
% 0.51/1.04  --schedule                              default
% 0.51/1.04  --add_important_lit                     false
% 0.51/1.04  --prop_solver_per_cl                    1000
% 0.51/1.04  --min_unsat_core                        false
% 0.51/1.04  --soft_assumptions                      false
% 0.51/1.04  --soft_lemma_size                       3
% 0.51/1.04  --prop_impl_unit_size                   0
% 0.51/1.04  --prop_impl_unit                        []
% 0.51/1.04  --share_sel_clauses                     true
% 0.51/1.04  --reset_solvers                         false
% 0.51/1.04  --bc_imp_inh                            [conj_cone]
% 0.51/1.04  --conj_cone_tolerance                   3.
% 0.51/1.04  --extra_neg_conj                        none
% 0.51/1.04  --large_theory_mode                     true
% 0.51/1.04  --prolific_symb_bound                   200
% 0.51/1.04  --lt_threshold                          2000
% 0.51/1.04  --clause_weak_htbl                      true
% 0.51/1.04  --gc_record_bc_elim                     false
% 0.51/1.04  
% 0.51/1.04  ------ Preprocessing Options
% 0.51/1.04  
% 0.51/1.04  --preprocessing_flag                    true
% 0.51/1.04  --time_out_prep_mult                    0.1
% 0.51/1.04  --splitting_mode                        input
% 0.51/1.04  --splitting_grd                         true
% 0.51/1.04  --splitting_cvd                         false
% 0.51/1.04  --splitting_cvd_svl                     false
% 0.51/1.04  --splitting_nvd                         32
% 0.51/1.04  --sub_typing                            true
% 0.51/1.04  --prep_gs_sim                           true
% 0.51/1.04  --prep_unflatten                        true
% 0.51/1.04  --prep_res_sim                          true
% 0.51/1.04  --prep_upred                            true
% 0.51/1.04  --prep_sem_filter                       exhaustive
% 0.51/1.04  --prep_sem_filter_out                   false
% 0.51/1.04  --pred_elim                             true
% 0.51/1.04  --res_sim_input                         true
% 0.51/1.04  --eq_ax_congr_red                       true
% 0.51/1.04  --pure_diseq_elim                       true
% 0.51/1.04  --brand_transform                       false
% 0.51/1.04  --non_eq_to_eq                          false
% 0.51/1.04  --prep_def_merge                        true
% 0.51/1.04  --prep_def_merge_prop_impl              false
% 0.51/1.04  --prep_def_merge_mbd                    true
% 0.51/1.04  --prep_def_merge_tr_red                 false
% 0.51/1.04  --prep_def_merge_tr_cl                  false
% 0.51/1.04  --smt_preprocessing                     true
% 0.51/1.04  --smt_ac_axioms                         fast
% 0.51/1.04  --preprocessed_out                      false
% 0.51/1.04  --preprocessed_stats                    false
% 0.51/1.04  
% 0.51/1.04  ------ Abstraction refinement Options
% 0.51/1.04  
% 0.51/1.04  --abstr_ref                             []
% 0.51/1.04  --abstr_ref_prep                        false
% 0.51/1.04  --abstr_ref_until_sat                   false
% 0.51/1.04  --abstr_ref_sig_restrict                funpre
% 0.51/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.51/1.04  --abstr_ref_under                       []
% 0.51/1.04  
% 0.51/1.04  ------ SAT Options
% 0.51/1.04  
% 0.51/1.04  --sat_mode                              false
% 0.51/1.04  --sat_fm_restart_options                ""
% 0.51/1.04  --sat_gr_def                            false
% 0.51/1.04  --sat_epr_types                         true
% 0.51/1.04  --sat_non_cyclic_types                  false
% 0.51/1.04  --sat_finite_models                     false
% 0.51/1.04  --sat_fm_lemmas                         false
% 0.51/1.04  --sat_fm_prep                           false
% 0.51/1.04  --sat_fm_uc_incr                        true
% 0.51/1.04  --sat_out_model                         small
% 0.51/1.04  --sat_out_clauses                       false
% 0.51/1.04  
% 0.51/1.04  ------ QBF Options
% 0.51/1.04  
% 0.51/1.04  --qbf_mode                              false
% 0.51/1.04  --qbf_elim_univ                         false
% 0.51/1.04  --qbf_dom_inst                          none
% 0.51/1.04  --qbf_dom_pre_inst                      false
% 0.51/1.04  --qbf_sk_in                             false
% 0.51/1.04  --qbf_pred_elim                         true
% 0.51/1.04  --qbf_split                             512
% 0.51/1.04  
% 0.51/1.04  ------ BMC1 Options
% 0.51/1.04  
% 0.51/1.04  --bmc1_incremental                      false
% 0.51/1.04  --bmc1_axioms                           reachable_all
% 0.51/1.04  --bmc1_min_bound                        0
% 0.51/1.04  --bmc1_max_bound                        -1
% 0.51/1.04  --bmc1_max_bound_default                -1
% 0.51/1.04  --bmc1_symbol_reachability              true
% 0.51/1.04  --bmc1_property_lemmas                  false
% 0.51/1.04  --bmc1_k_induction                      false
% 0.51/1.04  --bmc1_non_equiv_states                 false
% 0.51/1.04  --bmc1_deadlock                         false
% 0.51/1.04  --bmc1_ucm                              false
% 0.51/1.04  --bmc1_add_unsat_core                   none
% 0.51/1.04  --bmc1_unsat_core_children              false
% 0.51/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.51/1.04  --bmc1_out_stat                         full
% 0.51/1.04  --bmc1_ground_init                      false
% 0.51/1.04  --bmc1_pre_inst_next_state              false
% 0.51/1.04  --bmc1_pre_inst_state                   false
% 0.51/1.04  --bmc1_pre_inst_reach_state             false
% 0.51/1.04  --bmc1_out_unsat_core                   false
% 0.51/1.04  --bmc1_aig_witness_out                  false
% 0.51/1.04  --bmc1_verbose                          false
% 0.51/1.04  --bmc1_dump_clauses_tptp                false
% 0.51/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.51/1.04  --bmc1_dump_file                        -
% 0.51/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.51/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.51/1.04  --bmc1_ucm_extend_mode                  1
% 0.51/1.04  --bmc1_ucm_init_mode                    2
% 0.51/1.04  --bmc1_ucm_cone_mode                    none
% 0.51/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.51/1.04  --bmc1_ucm_relax_model                  4
% 0.51/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.51/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.51/1.04  --bmc1_ucm_layered_model                none
% 0.51/1.04  --bmc1_ucm_max_lemma_size               10
% 0.51/1.04  
% 0.51/1.04  ------ AIG Options
% 0.51/1.04  
% 0.51/1.04  --aig_mode                              false
% 0.51/1.04  
% 0.51/1.04  ------ Instantiation Options
% 0.51/1.04  
% 0.51/1.04  --instantiation_flag                    true
% 0.51/1.04  --inst_sos_flag                         false
% 0.51/1.04  --inst_sos_phase                        true
% 0.51/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.51/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.51/1.04  --inst_lit_sel_side                     none
% 0.51/1.04  --inst_solver_per_active                1400
% 0.51/1.04  --inst_solver_calls_frac                1.
% 0.51/1.04  --inst_passive_queue_type               priority_queues
% 0.51/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.51/1.04  --inst_passive_queues_freq              [25;2]
% 0.51/1.04  --inst_dismatching                      true
% 0.51/1.04  --inst_eager_unprocessed_to_passive     true
% 0.51/1.04  --inst_prop_sim_given                   true
% 0.51/1.04  --inst_prop_sim_new                     false
% 0.51/1.04  --inst_subs_new                         false
% 0.51/1.04  --inst_eq_res_simp                      false
% 0.51/1.04  --inst_subs_given                       false
% 0.51/1.04  --inst_orphan_elimination               true
% 0.51/1.04  --inst_learning_loop_flag               true
% 0.51/1.04  --inst_learning_start                   3000
% 0.51/1.04  --inst_learning_factor                  2
% 0.51/1.04  --inst_start_prop_sim_after_learn       3
% 0.51/1.04  --inst_sel_renew                        solver
% 0.51/1.04  --inst_lit_activity_flag                true
% 0.51/1.04  --inst_restr_to_given                   false
% 0.51/1.04  --inst_activity_threshold               500
% 0.51/1.04  --inst_out_proof                        true
% 0.51/1.04  
% 0.51/1.04  ------ Resolution Options
% 0.51/1.04  
% 0.51/1.04  --resolution_flag                       false
% 0.51/1.04  --res_lit_sel                           adaptive
% 0.51/1.04  --res_lit_sel_side                      none
% 0.51/1.04  --res_ordering                          kbo
% 0.51/1.04  --res_to_prop_solver                    active
% 0.51/1.04  --res_prop_simpl_new                    false
% 0.51/1.04  --res_prop_simpl_given                  true
% 0.51/1.04  --res_passive_queue_type                priority_queues
% 0.51/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.51/1.04  --res_passive_queues_freq               [15;5]
% 0.51/1.04  --res_forward_subs                      full
% 0.51/1.04  --res_backward_subs                     full
% 0.51/1.04  --res_forward_subs_resolution           true
% 0.51/1.04  --res_backward_subs_resolution          true
% 0.51/1.04  --res_orphan_elimination                true
% 0.51/1.04  --res_time_limit                        2.
% 0.51/1.04  --res_out_proof                         true
% 0.51/1.04  
% 0.51/1.04  ------ Superposition Options
% 0.51/1.04  
% 0.51/1.04  --superposition_flag                    true
% 0.51/1.04  --sup_passive_queue_type                priority_queues
% 0.51/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.51/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.51/1.04  --demod_completeness_check              fast
% 0.51/1.04  --demod_use_ground                      true
% 0.51/1.04  --sup_to_prop_solver                    passive
% 0.51/1.04  --sup_prop_simpl_new                    true
% 0.51/1.04  --sup_prop_simpl_given                  true
% 0.51/1.04  --sup_fun_splitting                     false
% 0.51/1.04  --sup_smt_interval                      50000
% 0.51/1.04  
% 0.51/1.04  ------ Superposition Simplification Setup
% 0.51/1.04  
% 0.51/1.04  --sup_indices_passive                   []
% 0.51/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.51/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.04  --sup_full_bw                           [BwDemod]
% 0.51/1.04  --sup_immed_triv                        [TrivRules]
% 0.51/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.51/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.04  --sup_immed_bw_main                     []
% 0.51/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.51/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.04  
% 0.51/1.04  ------ Combination Options
% 0.51/1.04  
% 0.51/1.04  --comb_res_mult                         3
% 0.51/1.04  --comb_sup_mult                         2
% 0.51/1.04  --comb_inst_mult                        10
% 0.51/1.04  
% 0.51/1.04  ------ Debug Options
% 0.51/1.04  
% 0.51/1.04  --dbg_backtrace                         false
% 0.51/1.04  --dbg_dump_prop_clauses                 false
% 0.51/1.04  --dbg_dump_prop_clauses_file            -
% 0.51/1.04  --dbg_out_stat                          false
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  ------ Proving...
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  % SZS status Theorem for theBenchmark.p
% 0.51/1.04  
% 0.51/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.51/1.04  
% 0.51/1.04  fof(f5,axiom,(
% 0.51/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f15,plain,(
% 0.51/1.04    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.04    inference(ennf_transformation,[],[f5])).
% 0.51/1.04  
% 0.51/1.04  fof(f33,plain,(
% 0.51/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.04    inference(cnf_transformation,[],[f15])).
% 0.51/1.04  
% 0.51/1.04  fof(f9,conjecture,(
% 0.51/1.04    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f10,negated_conjecture,(
% 0.51/1.04    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 0.51/1.04    inference(negated_conjecture,[],[f9])).
% 0.51/1.04  
% 0.51/1.04  fof(f21,plain,(
% 0.51/1.04    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.51/1.04    inference(ennf_transformation,[],[f10])).
% 0.51/1.04  
% 0.51/1.04  fof(f22,plain,(
% 0.51/1.04    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.51/1.04    inference(flattening,[],[f21])).
% 0.51/1.04  
% 0.51/1.04  fof(f26,plain,(
% 0.51/1.04    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 0.51/1.04    introduced(choice_axiom,[])).
% 0.51/1.04  
% 0.51/1.04  fof(f25,plain,(
% 0.51/1.04    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 0.51/1.04    introduced(choice_axiom,[])).
% 0.51/1.04  
% 0.51/1.04  fof(f24,plain,(
% 0.51/1.04    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.51/1.04    introduced(choice_axiom,[])).
% 0.51/1.04  
% 0.51/1.04  fof(f27,plain,(
% 0.51/1.04    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.51/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25,f24])).
% 0.51/1.04  
% 0.51/1.04  fof(f43,plain,(
% 0.51/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.51/1.04    inference(cnf_transformation,[],[f27])).
% 0.51/1.04  
% 0.51/1.04  fof(f8,axiom,(
% 0.51/1.04    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f20,plain,(
% 0.51/1.04    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.51/1.04    inference(ennf_transformation,[],[f8])).
% 0.51/1.04  
% 0.51/1.04  fof(f38,plain,(
% 0.51/1.04    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.51/1.04    inference(cnf_transformation,[],[f20])).
% 0.51/1.04  
% 0.51/1.04  fof(f39,plain,(
% 0.51/1.04    l1_struct_0(sK0)),
% 0.51/1.04    inference(cnf_transformation,[],[f27])).
% 0.51/1.04  
% 0.51/1.04  fof(f40,plain,(
% 0.51/1.04    l1_struct_0(sK1)),
% 0.51/1.04    inference(cnf_transformation,[],[f27])).
% 0.51/1.04  
% 0.51/1.04  fof(f7,axiom,(
% 0.51/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f18,plain,(
% 0.51/1.04    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.51/1.04    inference(ennf_transformation,[],[f7])).
% 0.51/1.04  
% 0.51/1.04  fof(f19,plain,(
% 0.51/1.04    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.51/1.04    inference(flattening,[],[f18])).
% 0.51/1.04  
% 0.51/1.04  fof(f36,plain,(
% 0.51/1.04    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.51/1.04    inference(cnf_transformation,[],[f19])).
% 0.51/1.04  
% 0.51/1.04  fof(f42,plain,(
% 0.51/1.04    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.51/1.04    inference(cnf_transformation,[],[f27])).
% 0.51/1.04  
% 0.51/1.04  fof(f41,plain,(
% 0.51/1.04    v1_funct_1(sK2)),
% 0.51/1.04    inference(cnf_transformation,[],[f27])).
% 0.51/1.04  
% 0.51/1.04  fof(f6,axiom,(
% 0.51/1.04    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f16,plain,(
% 0.51/1.04    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.51/1.04    inference(ennf_transformation,[],[f6])).
% 0.51/1.04  
% 0.51/1.04  fof(f17,plain,(
% 0.51/1.04    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.51/1.04    inference(flattening,[],[f16])).
% 0.51/1.04  
% 0.51/1.04  fof(f23,plain,(
% 0.51/1.04    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.51/1.04    inference(nnf_transformation,[],[f17])).
% 0.51/1.04  
% 0.51/1.04  fof(f34,plain,(
% 0.51/1.04    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.51/1.04    inference(cnf_transformation,[],[f23])).
% 0.51/1.04  
% 0.51/1.04  fof(f3,axiom,(
% 0.51/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f11,plain,(
% 0.51/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.51/1.04    inference(pure_predicate_removal,[],[f3])).
% 0.51/1.04  
% 0.51/1.04  fof(f13,plain,(
% 0.51/1.04    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.04    inference(ennf_transformation,[],[f11])).
% 0.51/1.04  
% 0.51/1.04  fof(f30,plain,(
% 0.51/1.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.04    inference(cnf_transformation,[],[f13])).
% 0.51/1.04  
% 0.51/1.04  fof(f1,axiom,(
% 0.51/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f12,plain,(
% 0.51/1.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.51/1.04    inference(ennf_transformation,[],[f1])).
% 0.51/1.04  
% 0.51/1.04  fof(f28,plain,(
% 0.51/1.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.51/1.04    inference(cnf_transformation,[],[f12])).
% 0.51/1.04  
% 0.51/1.04  fof(f2,axiom,(
% 0.51/1.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f29,plain,(
% 0.51/1.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.51/1.04    inference(cnf_transformation,[],[f2])).
% 0.51/1.04  
% 0.51/1.04  fof(f44,plain,(
% 0.51/1.04    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.51/1.04    inference(cnf_transformation,[],[f27])).
% 0.51/1.04  
% 0.51/1.04  fof(f32,plain,(
% 0.51/1.04    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.04    inference(cnf_transformation,[],[f15])).
% 0.51/1.04  
% 0.51/1.04  fof(f4,axiom,(
% 0.51/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.51/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.04  
% 0.51/1.04  fof(f14,plain,(
% 0.51/1.04    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.04    inference(ennf_transformation,[],[f4])).
% 0.51/1.04  
% 0.51/1.04  fof(f31,plain,(
% 0.51/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.04    inference(cnf_transformation,[],[f14])).
% 0.51/1.04  
% 0.51/1.04  fof(f45,plain,(
% 0.51/1.04    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 0.51/1.04    inference(cnf_transformation,[],[f27])).
% 0.51/1.04  
% 0.51/1.04  fof(f37,plain,(
% 0.51/1.04    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.51/1.04    inference(cnf_transformation,[],[f19])).
% 0.51/1.04  
% 0.51/1.04  fof(f47,plain,(
% 0.51/1.04    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.51/1.04    inference(equality_resolution,[],[f37])).
% 0.51/1.04  
% 0.51/1.04  cnf(c_4,plain,
% 0.51/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.04      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f33]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_13,negated_conjecture,
% 0.51/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 0.51/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_299,plain,
% 0.51/1.04      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.51/1.04      | sK2 != X2 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_300,plain,
% 0.51/1.04      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_299]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_496,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 0.51/1.04      | k8_relset_1(X0_49,X1_49,sK2,X1_49) = k1_relset_1(X0_49,X1_49,sK2) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_300]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_10,plain,
% 0.51/1.04      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f38]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_17,negated_conjecture,
% 0.51/1.04      ( l1_struct_0(sK0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_191,plain,
% 0.51/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_192,plain,
% 0.51/1.04      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_191]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_499,plain,
% 0.51/1.04      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_192]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_16,negated_conjecture,
% 0.51/1.04      ( l1_struct_0(sK1) ),
% 0.51/1.04      inference(cnf_transformation,[],[f40]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_186,plain,
% 0.51/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_187,plain,
% 0.51/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_186]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_500,plain,
% 0.51/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_187]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_700,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 0.51/1.04      | k8_relset_1(X0_49,X1_49,sK2,X1_49) = k1_relset_1(X0_49,X1_49,sK2) ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_496,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1049,plain,
% 0.51/1.04      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 0.51/1.04      inference(equality_resolution,[status(thm)],[c_700]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_9,plain,
% 0.51/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 0.51/1.04      | v1_partfun1(X0,X1)
% 0.51/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.04      | ~ v1_funct_1(X0)
% 0.51/1.04      | k1_xboole_0 = X2 ),
% 0.51/1.04      inference(cnf_transformation,[],[f36]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_14,negated_conjecture,
% 0.51/1.04      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 0.51/1.04      inference(cnf_transformation,[],[f42]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_254,plain,
% 0.51/1.04      ( v1_partfun1(X0,X1)
% 0.51/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.04      | ~ v1_funct_1(X0)
% 0.51/1.04      | u1_struct_0(sK1) != X2
% 0.51/1.04      | u1_struct_0(sK0) != X1
% 0.51/1.04      | sK2 != X0
% 0.51/1.04      | k1_xboole_0 = X2 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_255,plain,
% 0.51/1.04      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 0.51/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 0.51/1.04      | ~ v1_funct_1(sK2)
% 0.51/1.04      | k1_xboole_0 = u1_struct_0(sK1) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_254]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_15,negated_conjecture,
% 0.51/1.04      ( v1_funct_1(sK2) ),
% 0.51/1.04      inference(cnf_transformation,[],[f41]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_257,plain,
% 0.51/1.04      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 0.51/1.04      | k1_xboole_0 = u1_struct_0(sK1) ),
% 0.51/1.04      inference(global_propositional_subsumption,
% 0.51/1.04                [status(thm)],
% 0.51/1.04                [c_255,c_15,c_13]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_7,plain,
% 0.51/1.04      ( ~ v1_partfun1(X0,X1)
% 0.51/1.04      | ~ v4_relat_1(X0,X1)
% 0.51/1.04      | ~ v1_relat_1(X0)
% 0.51/1.04      | k1_relat_1(X0) = X1 ),
% 0.51/1.04      inference(cnf_transformation,[],[f34]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_2,plain,
% 0.51/1.04      ( v4_relat_1(X0,X1)
% 0.51/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.51/1.04      inference(cnf_transformation,[],[f30]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_317,plain,
% 0.51/1.04      ( v4_relat_1(X0,X1)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.51/1.04      | sK2 != X0 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_318,plain,
% 0.51/1.04      ( v4_relat_1(sK2,X0)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_317]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_362,plain,
% 0.51/1.04      ( ~ v1_partfun1(X0,X1)
% 0.51/1.04      | ~ v1_relat_1(X0)
% 0.51/1.04      | X2 != X1
% 0.51/1.04      | k1_relat_1(X0) = X1
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 0.51/1.04      | sK2 != X0 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_318]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_363,plain,
% 0.51/1.04      ( ~ v1_partfun1(sK2,X0)
% 0.51/1.04      | ~ v1_relat_1(sK2)
% 0.51/1.04      | k1_relat_1(sK2) = X0
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_362]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_425,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | u1_struct_0(sK1) = k1_xboole_0
% 0.51/1.04      | u1_struct_0(sK0) != X0
% 0.51/1.04      | k1_relat_1(sK2) = X0
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.51/1.04      | sK2 != sK2 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_257,c_363]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_426,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | u1_struct_0(sK1) = k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_425]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_493,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_49))
% 0.51/1.04      | u1_struct_0(sK1) = k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_426]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_507,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | sP1_iProver_split
% 0.51/1.04      | u1_struct_0(sK1) = k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 0.51/1.04      inference(splitting,
% 0.51/1.04                [splitting(split),new_symbols(definition,[])],
% 0.51/1.04                [c_493]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_649,plain,
% 0.51/1.04      ( u1_struct_0(sK1) = k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 0.51/1.04      | v1_relat_1(sK2) != iProver_top
% 0.51/1.04      | sP1_iProver_split = iProver_top ),
% 0.51/1.04      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_679,plain,
% 0.51/1.04      ( k2_struct_0(sK1) = k1_xboole_0
% 0.51/1.04      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 0.51/1.04      | v1_relat_1(sK2) != iProver_top
% 0.51/1.04      | sP1_iProver_split = iProver_top ),
% 0.51/1.04      inference(demodulation,[status(thm)],[c_649,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_511,plain,( X0_51 = X0_51 ),theory(equality) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_744,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 0.51/1.04      inference(instantiation,[status(thm)],[c_511]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_506,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_49))
% 0.51/1.04      | ~ sP1_iProver_split ),
% 0.51/1.04      inference(splitting,
% 0.51/1.04                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.51/1.04                [c_493]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_650,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_49))
% 0.51/1.04      | sP1_iProver_split != iProver_top ),
% 0.51/1.04      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_669,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_49))
% 0.51/1.04      | sP1_iProver_split != iProver_top ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_650,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_778,plain,
% 0.51/1.04      ( sP1_iProver_split != iProver_top ),
% 0.51/1.04      inference(equality_resolution,[status(thm)],[c_669]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_0,plain,
% 0.51/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.51/1.04      | ~ v1_relat_1(X1)
% 0.51/1.04      | v1_relat_1(X0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f28]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_275,plain,
% 0.51/1.04      ( ~ v1_relat_1(X0)
% 0.51/1.04      | v1_relat_1(X1)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 0.51/1.04      | sK2 != X1 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_276,plain,
% 0.51/1.04      ( ~ v1_relat_1(X0)
% 0.51/1.04      | v1_relat_1(sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_275]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_498,plain,
% 0.51/1.04      ( ~ v1_relat_1(X0_48)
% 0.51/1.04      | v1_relat_1(sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_48) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_276]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_739,plain,
% 0.51/1.04      ( ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
% 0.51/1.04      | v1_relat_1(sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 0.51/1.04      inference(instantiation,[status(thm)],[c_498]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_784,plain,
% 0.51/1.04      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 0.51/1.04      | v1_relat_1(sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 0.51/1.04      inference(instantiation,[status(thm)],[c_739]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_785,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 0.51/1.04      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 0.51/1.04      | v1_relat_1(sK2) = iProver_top ),
% 0.51/1.04      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1,plain,
% 0.51/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.51/1.04      inference(cnf_transformation,[],[f29]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_503,plain,
% 0.51/1.04      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_806,plain,
% 0.51/1.04      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 0.51/1.04      inference(instantiation,[status(thm)],[c_503]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_807,plain,
% 0.51/1.04      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 0.51/1.04      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_861,plain,
% 0.51/1.04      ( k2_struct_0(sK1) = k1_xboole_0
% 0.51/1.04      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 0.51/1.04      inference(global_propositional_subsumption,
% 0.51/1.04                [status(thm)],
% 0.51/1.04                [c_679,c_744,c_778,c_785,c_807]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_12,negated_conjecture,
% 0.51/1.04      ( k1_xboole_0 != k2_struct_0(sK1)
% 0.51/1.04      | k1_xboole_0 = k2_struct_0(sK0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_501,negated_conjecture,
% 0.51/1.04      ( k1_xboole_0 != k2_struct_0(sK1)
% 0.51/1.04      | k1_xboole_0 = k2_struct_0(sK0) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_12]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_870,plain,
% 0.51/1.04      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(superposition,[status(thm)],[c_861,c_501]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_5,plain,
% 0.51/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.04      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f32]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_290,plain,
% 0.51/1.04      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.51/1.04      | sK2 != X2 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_291,plain,
% 0.51/1.04      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_290]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_497,plain,
% 0.51/1.04      ( k7_relset_1(X0_49,X1_49,sK2,X0_49) = k2_relset_1(X0_49,X1_49,sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_291]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_695,plain,
% 0.51/1.04      ( k7_relset_1(X0_49,X1_49,sK2,X0_49) = k2_relset_1(X0_49,X1_49,sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_497,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1028,plain,
% 0.51/1.04      ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 0.51/1.04      inference(equality_resolution,[status(thm)],[c_695]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1432,plain,
% 0.51/1.04      ( k7_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k1_relat_1(sK2)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(superposition,[status(thm)],[c_870,c_1028]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_3,plain,
% 0.51/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f31]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_308,plain,
% 0.51/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.51/1.04      | sK2 != X2 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_309,plain,
% 0.51/1.04      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_308]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_495,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 0.51/1.04      | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_309]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_674,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 0.51/1.04      | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_495,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_916,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 0.51/1.04      | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(superposition,[status(thm)],[c_870,c_674]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1113,plain,
% 0.51/1.04      ( k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(equality_resolution,[status(thm)],[c_916]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1047,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 0.51/1.04      | k8_relset_1(X0_49,X1_49,sK2,X1_49) = k1_relset_1(X0_49,X1_49,sK2)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(superposition,[status(thm)],[c_870,c_700]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1155,plain,
% 0.51/1.04      ( k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(equality_resolution,[status(thm)],[c_1047]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_11,negated_conjecture,
% 0.51/1.04      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_502,negated_conjecture,
% 0.51/1.04      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_11]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_661,plain,
% 0.51/1.04      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_502,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_920,plain,
% 0.51/1.04      ( k8_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(superposition,[status(thm)],[c_870,c_661]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1343,plain,
% 0.51/1.04      ( k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) != k2_struct_0(sK0)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(superposition,[status(thm)],[c_1155,c_920]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1350,plain,
% 0.51/1.04      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 0.51/1.04      | k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(superposition,[status(thm)],[c_1113,c_1343]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1441,plain,
% 0.51/1.04      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 0.51/1.04      inference(global_propositional_subsumption,
% 0.51/1.04                [status(thm)],
% 0.51/1.04                [c_1432,c_870,c_1350]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1549,plain,
% 0.51/1.04      ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_1049,c_1441]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1461,plain,
% 0.51/1.04      ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k1_xboole_0 ),
% 0.51/1.04      inference(demodulation,[status(thm)],[c_1441,c_661]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1551,plain,
% 0.51/1.04      ( k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) != k1_xboole_0 ),
% 0.51/1.04      inference(demodulation,[status(thm)],[c_1549,c_1461]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_8,plain,
% 0.51/1.04      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.51/1.04      | v1_partfun1(X0,k1_xboole_0)
% 0.51/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.51/1.04      | ~ v1_funct_1(X0) ),
% 0.51/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_237,plain,
% 0.51/1.04      ( v1_partfun1(X0,k1_xboole_0)
% 0.51/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.51/1.04      | ~ v1_funct_1(X0)
% 0.51/1.04      | u1_struct_0(sK1) != X1
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | sK2 != X0 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_238,plain,
% 0.51/1.04      ( v1_partfun1(sK2,k1_xboole_0)
% 0.51/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 0.51/1.04      | ~ v1_funct_1(sK2)
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0 ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_237]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_240,plain,
% 0.51/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 0.51/1.04      | v1_partfun1(sK2,k1_xboole_0)
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0 ),
% 0.51/1.04      inference(global_propositional_subsumption,
% 0.51/1.04                [status(thm)],
% 0.51/1.04                [c_238,c_15]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_241,plain,
% 0.51/1.04      ( v1_partfun1(sK2,k1_xboole_0)
% 0.51/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0 ),
% 0.51/1.04      inference(renaming,[status(thm)],[c_240]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_329,plain,
% 0.51/1.04      ( v1_partfun1(sK2,k1_xboole_0)
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 0.51/1.04      | sK2 != sK2 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_241]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_404,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = X0
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 0.51/1.04      | sK2 != sK2
% 0.51/1.04      | k1_xboole_0 != X0 ),
% 0.51/1.04      inference(resolution_lifted,[status(thm)],[c_329,c_363]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_405,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
% 0.51/1.04      inference(unflattening,[status(thm)],[c_404]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_494,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0 ),
% 0.51/1.04      inference(subtyping,[status(esa)],[c_405]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_505,plain,
% 0.51/1.04      ( ~ v1_relat_1(sK2)
% 0.51/1.04      | sP0_iProver_split
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0 ),
% 0.51/1.04      inference(splitting,
% 0.51/1.04                [splitting(split),new_symbols(definition,[])],
% 0.51/1.04                [c_494]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_647,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 0.51/1.04      | u1_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0
% 0.51/1.04      | v1_relat_1(sK2) != iProver_top
% 0.51/1.04      | sP0_iProver_split = iProver_top ),
% 0.51/1.04      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_705,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 0.51/1.04      | k2_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0
% 0.51/1.04      | v1_relat_1(sK2) != iProver_top
% 0.51/1.04      | sP0_iProver_split = iProver_top ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_647,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_504,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
% 0.51/1.04      | ~ sP0_iProver_split ),
% 0.51/1.04      inference(splitting,
% 0.51/1.04                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.51/1.04                [c_494]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_648,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
% 0.51/1.04      | sP0_iProver_split != iProver_top ),
% 0.51/1.04      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_664,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_49))
% 0.51/1.04      | sP0_iProver_split != iProver_top ),
% 0.51/1.04      inference(light_normalisation,[status(thm)],[c_648,c_499,c_500]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_711,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 0.51/1.04      | k2_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0
% 0.51/1.04      | v1_relat_1(sK2) != iProver_top ),
% 0.51/1.04      inference(forward_subsumption_resolution,
% 0.51/1.04                [status(thm)],
% 0.51/1.04                [c_705,c_664]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1231,plain,
% 0.51/1.04      ( k1_relat_1(sK2) = k1_xboole_0
% 0.51/1.04      | k2_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) ),
% 0.51/1.04      inference(global_propositional_subsumption,
% 0.51/1.04                [status(thm)],
% 0.51/1.04                [c_711,c_744,c_785,c_807]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1232,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 0.51/1.04      | k2_struct_0(sK0) != k1_xboole_0
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0 ),
% 0.51/1.04      inference(renaming,[status(thm)],[c_1231]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1446,plain,
% 0.51/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 0.51/1.04      | k1_relat_1(sK2) = k1_xboole_0
% 0.51/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 0.51/1.04      inference(demodulation,[status(thm)],[c_1441,c_1232]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1494,plain,
% 0.51/1.04      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 0.51/1.04      inference(equality_resolution_simp,[status(thm)],[c_1446]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_824,plain,
% 0.51/1.04      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 0.51/1.04      inference(equality_resolution,[status(thm)],[c_674]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1447,plain,
% 0.51/1.04      ( k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 0.51/1.04      inference(demodulation,[status(thm)],[c_1441,c_824]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(c_1496,plain,
% 0.51/1.04      ( k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) = k1_xboole_0 ),
% 0.51/1.04      inference(demodulation,[status(thm)],[c_1494,c_1447]) ).
% 0.51/1.04  
% 0.51/1.04  cnf(contradiction,plain,
% 0.51/1.04      ( $false ),
% 0.51/1.04      inference(minisat,[status(thm)],[c_1551,c_1496]) ).
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.51/1.04  
% 0.51/1.04  ------                               Statistics
% 0.51/1.04  
% 0.51/1.04  ------ General
% 0.51/1.04  
% 0.51/1.04  abstr_ref_over_cycles:                  0
% 0.51/1.04  abstr_ref_under_cycles:                 0
% 0.51/1.04  gc_basic_clause_elim:                   0
% 0.51/1.04  forced_gc_time:                         0
% 0.51/1.04  parsing_time:                           0.008
% 0.51/1.04  unif_index_cands_time:                  0.
% 0.51/1.04  unif_index_add_time:                    0.
% 0.51/1.04  orderings_time:                         0.
% 0.51/1.04  out_proof_time:                         0.008
% 0.51/1.04  total_time:                             0.077
% 0.51/1.04  num_of_symbols:                         55
% 0.51/1.04  num_of_terms:                           1389
% 0.51/1.04  
% 0.51/1.04  ------ Preprocessing
% 0.51/1.04  
% 0.51/1.04  num_of_splits:                          2
% 0.51/1.04  num_of_split_atoms:                     2
% 0.51/1.04  num_of_reused_defs:                     0
% 0.51/1.04  num_eq_ax_congr_red:                    29
% 0.51/1.04  num_of_sem_filtered_clauses:            6
% 0.51/1.04  num_of_subtypes:                        5
% 0.51/1.04  monotx_restored_types:                  0
% 0.51/1.04  sat_num_of_epr_types:                   0
% 0.51/1.04  sat_num_of_non_cyclic_types:            0
% 0.51/1.04  sat_guarded_non_collapsed_types:        0
% 0.51/1.04  num_pure_diseq_elim:                    0
% 0.51/1.04  simp_replaced_by:                       0
% 0.51/1.04  res_preprocessed:                       81
% 0.51/1.04  prep_upred:                             0
% 0.51/1.04  prep_unflattend:                        21
% 0.51/1.04  smt_new_axioms:                         0
% 0.51/1.04  pred_elim_cands:                        1
% 0.51/1.04  pred_elim:                              6
% 0.51/1.04  pred_elim_cl:                           7
% 0.51/1.04  pred_elim_cycles:                       9
% 0.51/1.04  merged_defs:                            0
% 0.51/1.04  merged_defs_ncl:                        0
% 0.51/1.04  bin_hyper_res:                          0
% 0.51/1.04  prep_cycles:                            4
% 0.51/1.04  pred_elim_time:                         0.005
% 0.51/1.04  splitting_time:                         0.
% 0.51/1.04  sem_filter_time:                        0.
% 0.51/1.04  monotx_time:                            0.
% 0.51/1.04  subtype_inf_time:                       0.
% 0.51/1.04  
% 0.51/1.04  ------ Problem properties
% 0.51/1.04  
% 0.51/1.04  clauses:                                13
% 0.51/1.04  conjectures:                            2
% 0.51/1.04  epr:                                    0
% 0.51/1.04  horn:                                   11
% 0.51/1.04  ground:                                 6
% 0.51/1.04  unary:                                  4
% 0.51/1.04  binary:                                 6
% 0.51/1.04  lits:                                   28
% 0.51/1.04  lits_eq:                                19
% 0.51/1.04  fd_pure:                                0
% 0.51/1.04  fd_pseudo:                              0
% 0.51/1.04  fd_cond:                                0
% 0.51/1.04  fd_pseudo_cond:                         0
% 0.51/1.04  ac_symbols:                             0
% 0.51/1.04  
% 0.51/1.04  ------ Propositional Solver
% 0.51/1.04  
% 0.51/1.04  prop_solver_calls:                      29
% 0.51/1.04  prop_fast_solver_calls:                 477
% 0.51/1.04  smt_solver_calls:                       0
% 0.51/1.04  smt_fast_solver_calls:                  0
% 0.51/1.04  prop_num_of_clauses:                    463
% 0.51/1.04  prop_preprocess_simplified:             1895
% 0.51/1.04  prop_fo_subsumed:                       9
% 0.51/1.04  prop_solver_time:                       0.
% 0.51/1.04  smt_solver_time:                        0.
% 0.51/1.04  smt_fast_solver_time:                   0.
% 0.51/1.04  prop_fast_solver_time:                  0.
% 0.51/1.04  prop_unsat_core_time:                   0.
% 0.51/1.04  
% 0.51/1.04  ------ QBF
% 0.51/1.04  
% 0.51/1.04  qbf_q_res:                              0
% 0.51/1.04  qbf_num_tautologies:                    0
% 0.51/1.04  qbf_prep_cycles:                        0
% 0.51/1.04  
% 0.51/1.04  ------ BMC1
% 0.51/1.04  
% 0.51/1.04  bmc1_current_bound:                     -1
% 0.51/1.04  bmc1_last_solved_bound:                 -1
% 0.51/1.04  bmc1_unsat_core_size:                   -1
% 0.51/1.04  bmc1_unsat_core_parents_size:           -1
% 0.51/1.04  bmc1_merge_next_fun:                    0
% 0.51/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.51/1.04  
% 0.51/1.04  ------ Instantiation
% 0.51/1.04  
% 0.51/1.04  inst_num_of_clauses:                    170
% 0.51/1.04  inst_num_in_passive:                    56
% 0.51/1.04  inst_num_in_active:                     102
% 0.51/1.04  inst_num_in_unprocessed:                12
% 0.51/1.04  inst_num_of_loops:                      160
% 0.51/1.04  inst_num_of_learning_restarts:          0
% 0.51/1.04  inst_num_moves_active_passive:          52
% 0.51/1.04  inst_lit_activity:                      0
% 0.51/1.04  inst_lit_activity_moves:                0
% 0.51/1.04  inst_num_tautologies:                   0
% 0.51/1.04  inst_num_prop_implied:                  0
% 0.51/1.04  inst_num_existing_simplified:           0
% 0.51/1.04  inst_num_eq_res_simplified:             0
% 0.51/1.04  inst_num_child_elim:                    0
% 0.51/1.04  inst_num_of_dismatching_blockings:      25
% 0.51/1.04  inst_num_of_non_proper_insts:           174
% 0.51/1.04  inst_num_of_duplicates:                 0
% 0.51/1.04  inst_inst_num_from_inst_to_res:         0
% 0.51/1.04  inst_dismatching_checking_time:         0.
% 0.51/1.04  
% 0.51/1.04  ------ Resolution
% 0.51/1.04  
% 0.51/1.04  res_num_of_clauses:                     0
% 0.51/1.04  res_num_in_passive:                     0
% 0.51/1.04  res_num_in_active:                      0
% 0.51/1.04  res_num_of_loops:                       85
% 0.51/1.04  res_forward_subset_subsumed:            85
% 0.51/1.04  res_backward_subset_subsumed:           0
% 0.51/1.04  res_forward_subsumed:                   0
% 0.51/1.04  res_backward_subsumed:                  0
% 0.51/1.04  res_forward_subsumption_resolution:     0
% 0.51/1.04  res_backward_subsumption_resolution:    0
% 0.51/1.04  res_clause_to_clause_subsumption:       51
% 0.51/1.04  res_orphan_elimination:                 0
% 0.51/1.04  res_tautology_del:                      33
% 0.51/1.04  res_num_eq_res_simplified:              0
% 0.51/1.04  res_num_sel_changes:                    0
% 0.51/1.04  res_moves_from_active_to_pass:          0
% 0.51/1.04  
% 0.51/1.04  ------ Superposition
% 0.51/1.04  
% 0.51/1.04  sup_time_total:                         0.
% 0.51/1.04  sup_time_generating:                    0.
% 0.51/1.04  sup_time_sim_full:                      0.
% 0.51/1.04  sup_time_sim_immed:                     0.
% 0.51/1.04  
% 0.51/1.04  sup_num_of_clauses:                     26
% 0.51/1.04  sup_num_in_active:                      10
% 0.51/1.04  sup_num_in_passive:                     16
% 0.51/1.04  sup_num_of_loops:                       31
% 0.51/1.04  sup_fw_superposition:                   24
% 0.51/1.04  sup_bw_superposition:                   12
% 0.51/1.04  sup_immediate_simplified:               17
% 0.51/1.04  sup_given_eliminated:                   0
% 0.51/1.04  comparisons_done:                       0
% 0.51/1.04  comparisons_avoided:                    12
% 0.51/1.04  
% 0.51/1.04  ------ Simplifications
% 0.51/1.04  
% 0.51/1.04  
% 0.51/1.04  sim_fw_subset_subsumed:                 13
% 0.51/1.04  sim_bw_subset_subsumed:                 0
% 0.51/1.04  sim_fw_subsumed:                        0
% 0.51/1.04  sim_bw_subsumed:                        1
% 0.51/1.04  sim_fw_subsumption_res:                 1
% 0.51/1.04  sim_bw_subsumption_res:                 0
% 0.51/1.04  sim_tautology_del:                      1
% 0.51/1.04  sim_eq_tautology_del:                   9
% 0.51/1.04  sim_eq_res_simp:                        1
% 0.51/1.04  sim_fw_demodulated:                     1
% 0.51/1.04  sim_bw_demodulated:                     24
% 0.51/1.04  sim_light_normalised:                   9
% 0.51/1.04  sim_joinable_taut:                      0
% 0.51/1.04  sim_joinable_simp:                      0
% 0.51/1.04  sim_ac_normalised:                      0
% 0.51/1.04  sim_smt_subsumption:                    0
% 0.51/1.04  
%------------------------------------------------------------------------------
