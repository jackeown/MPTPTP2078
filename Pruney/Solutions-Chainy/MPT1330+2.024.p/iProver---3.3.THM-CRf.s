%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:57 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  178 (2846 expanded)
%              Number of clauses        :  109 ( 875 expanded)
%              Number of leaves         :   20 ( 806 expanded)
%              Depth                    :   37
%              Number of atoms          :  548 (16637 expanded)
%              Number of equality atoms :  279 (6740 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f45,f44,f43])).

fof(f75,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f61,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f48])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_375,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_376,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_378,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_28,c_26])).

cnf(c_417,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) != X1
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_378])).

cnf(c_418,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_418])).

cnf(c_444,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_532,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) != k1_zfmisc_1(X1)
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_444])).

cnf(c_773,plain,
    ( ~ v1_relat_1(sK2)
    | sP1_iProver_split
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | sK2 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_532])).

cnf(c_1029,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | sK2 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_270,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_271,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_275,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_276,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_1147,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | sK2 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1029,c_271,c_276])).

cnf(c_618,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_444])).

cnf(c_697,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_618])).

cnf(c_771,plain,
    ( ~ v1_relat_1(sK2)
    | sP0_iProver_split
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_697])).

cnf(c_1025,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_1107,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1025,c_271,c_276])).

cnf(c_1184,plain,
    ( ~ v1_relat_1(sK2)
    | sP0_iProver_split
    | k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1107])).

cnf(c_777,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1231,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_770,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_697])).

cnf(c_1026,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_1092,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1026,c_271,c_276])).

cnf(c_1271,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1092])).

cnf(c_1272,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1271])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_561,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_562,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_1224,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_1341,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1487,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1534,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_1184,c_1231,c_1272,c_1341,c_1487])).

cnf(c_1535,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_1534])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1545,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1535,c_25])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_282,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_6])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
    inference(resolution,[status(thm)],[c_282,c_12])).

cnf(c_576,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_26])).

cnf(c_577,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_partfun1(X0)) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_1027,plain,
    ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_1140,plain,
    ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1027,c_271,c_276])).

cnf(c_1440,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1140])).

cnf(c_1454,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1440])).

cnf(c_2535,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1440,c_1231,c_1341,c_1454,c_1487])).

cnf(c_14,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1035,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1028,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1116,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1028,c_271,c_276])).

cnf(c_1598,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1116])).

cnf(c_1342,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1341])).

cnf(c_1488,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_1943,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1598,c_1231,c_1342,c_1488])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1036,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2859,plain,
    ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1943,c_1036])).

cnf(c_3067,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_partfun1(X0))) ),
    inference(superposition,[status(thm)],[c_1035,c_2859])).

cnf(c_11,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3076,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_3067,c_11])).

cnf(c_3475,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2535,c_3076])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_591,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_592,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_1135,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_592,c_271,c_276])).

cnf(c_1390,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_1135])).

cnf(c_24,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1062,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_24,c_271,c_276])).

cnf(c_2472,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1390,c_1062])).

cnf(c_3767,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3475,c_2472])).

cnf(c_3770,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1545,c_3767])).

cnf(c_3810,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3770,c_3767])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_358,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_359,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_361,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | v1_partfun1(sK2,k1_xboole_0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_28])).

cnf(c_362,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_398,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(X0) = X1
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_362])).

cnf(c_399,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_399,c_16])).

cnf(c_600,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_411])).

cnf(c_701,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_600])).

cnf(c_1024,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1169,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1024,c_271,c_276])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1170,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1169,c_1])).

cnf(c_3195,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k2_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_1231,c_1342,c_1488])).

cnf(c_3196,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_3195])).

cnf(c_3816,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3770,c_3196])).

cnf(c_3902,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(equality_resolution_simp,[status(thm)],[c_3816])).

cnf(c_3905,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3902,c_1])).

cnf(c_3906,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3905])).

cnf(c_3909,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3810,c_3906])).

cnf(c_3910,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3909])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:21:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.60/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.01  
% 2.60/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/1.01  
% 2.60/1.01  ------  iProver source info
% 2.60/1.01  
% 2.60/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.60/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/1.01  git: non_committed_changes: false
% 2.60/1.01  git: last_make_outside_of_git: false
% 2.60/1.01  
% 2.60/1.01  ------ 
% 2.60/1.01  
% 2.60/1.01  ------ Input Options
% 2.60/1.01  
% 2.60/1.01  --out_options                           all
% 2.60/1.01  --tptp_safe_out                         true
% 2.60/1.01  --problem_path                          ""
% 2.60/1.01  --include_path                          ""
% 2.60/1.01  --clausifier                            res/vclausify_rel
% 2.60/1.01  --clausifier_options                    --mode clausify
% 2.60/1.01  --stdin                                 false
% 2.60/1.01  --stats_out                             all
% 2.60/1.01  
% 2.60/1.01  ------ General Options
% 2.60/1.01  
% 2.60/1.01  --fof                                   false
% 2.60/1.01  --time_out_real                         305.
% 2.60/1.01  --time_out_virtual                      -1.
% 2.60/1.01  --symbol_type_check                     false
% 2.60/1.01  --clausify_out                          false
% 2.60/1.01  --sig_cnt_out                           false
% 2.60/1.01  --trig_cnt_out                          false
% 2.60/1.01  --trig_cnt_out_tolerance                1.
% 2.60/1.01  --trig_cnt_out_sk_spl                   false
% 2.60/1.01  --abstr_cl_out                          false
% 2.60/1.01  
% 2.60/1.01  ------ Global Options
% 2.60/1.01  
% 2.60/1.01  --schedule                              default
% 2.60/1.01  --add_important_lit                     false
% 2.60/1.01  --prop_solver_per_cl                    1000
% 2.60/1.01  --min_unsat_core                        false
% 2.60/1.01  --soft_assumptions                      false
% 2.60/1.01  --soft_lemma_size                       3
% 2.60/1.01  --prop_impl_unit_size                   0
% 2.60/1.01  --prop_impl_unit                        []
% 2.60/1.01  --share_sel_clauses                     true
% 2.60/1.01  --reset_solvers                         false
% 2.60/1.01  --bc_imp_inh                            [conj_cone]
% 2.60/1.01  --conj_cone_tolerance                   3.
% 2.60/1.01  --extra_neg_conj                        none
% 2.60/1.01  --large_theory_mode                     true
% 2.60/1.01  --prolific_symb_bound                   200
% 2.60/1.01  --lt_threshold                          2000
% 2.60/1.01  --clause_weak_htbl                      true
% 2.60/1.01  --gc_record_bc_elim                     false
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing Options
% 2.60/1.01  
% 2.60/1.01  --preprocessing_flag                    true
% 2.60/1.01  --time_out_prep_mult                    0.1
% 2.60/1.01  --splitting_mode                        input
% 2.60/1.01  --splitting_grd                         true
% 2.60/1.01  --splitting_cvd                         false
% 2.60/1.01  --splitting_cvd_svl                     false
% 2.60/1.01  --splitting_nvd                         32
% 2.60/1.01  --sub_typing                            true
% 2.60/1.01  --prep_gs_sim                           true
% 2.60/1.01  --prep_unflatten                        true
% 2.60/1.01  --prep_res_sim                          true
% 2.60/1.01  --prep_upred                            true
% 2.60/1.01  --prep_sem_filter                       exhaustive
% 2.60/1.01  --prep_sem_filter_out                   false
% 2.60/1.01  --pred_elim                             true
% 2.60/1.01  --res_sim_input                         true
% 2.60/1.01  --eq_ax_congr_red                       true
% 2.60/1.01  --pure_diseq_elim                       true
% 2.60/1.01  --brand_transform                       false
% 2.60/1.01  --non_eq_to_eq                          false
% 2.60/1.01  --prep_def_merge                        true
% 2.60/1.01  --prep_def_merge_prop_impl              false
% 2.60/1.01  --prep_def_merge_mbd                    true
% 2.60/1.01  --prep_def_merge_tr_red                 false
% 2.60/1.01  --prep_def_merge_tr_cl                  false
% 2.60/1.01  --smt_preprocessing                     true
% 2.60/1.01  --smt_ac_axioms                         fast
% 2.60/1.01  --preprocessed_out                      false
% 2.60/1.01  --preprocessed_stats                    false
% 2.60/1.01  
% 2.60/1.01  ------ Abstraction refinement Options
% 2.60/1.01  
% 2.60/1.01  --abstr_ref                             []
% 2.60/1.01  --abstr_ref_prep                        false
% 2.60/1.01  --abstr_ref_until_sat                   false
% 2.60/1.01  --abstr_ref_sig_restrict                funpre
% 2.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.01  --abstr_ref_under                       []
% 2.60/1.01  
% 2.60/1.01  ------ SAT Options
% 2.60/1.01  
% 2.60/1.01  --sat_mode                              false
% 2.60/1.01  --sat_fm_restart_options                ""
% 2.60/1.01  --sat_gr_def                            false
% 2.60/1.01  --sat_epr_types                         true
% 2.60/1.01  --sat_non_cyclic_types                  false
% 2.60/1.01  --sat_finite_models                     false
% 2.60/1.01  --sat_fm_lemmas                         false
% 2.60/1.01  --sat_fm_prep                           false
% 2.60/1.01  --sat_fm_uc_incr                        true
% 2.60/1.01  --sat_out_model                         small
% 2.60/1.01  --sat_out_clauses                       false
% 2.60/1.01  
% 2.60/1.01  ------ QBF Options
% 2.60/1.01  
% 2.60/1.01  --qbf_mode                              false
% 2.60/1.01  --qbf_elim_univ                         false
% 2.60/1.01  --qbf_dom_inst                          none
% 2.60/1.01  --qbf_dom_pre_inst                      false
% 2.60/1.01  --qbf_sk_in                             false
% 2.60/1.01  --qbf_pred_elim                         true
% 2.60/1.01  --qbf_split                             512
% 2.60/1.01  
% 2.60/1.01  ------ BMC1 Options
% 2.60/1.01  
% 2.60/1.01  --bmc1_incremental                      false
% 2.60/1.01  --bmc1_axioms                           reachable_all
% 2.60/1.01  --bmc1_min_bound                        0
% 2.60/1.01  --bmc1_max_bound                        -1
% 2.60/1.01  --bmc1_max_bound_default                -1
% 2.60/1.01  --bmc1_symbol_reachability              true
% 2.60/1.01  --bmc1_property_lemmas                  false
% 2.60/1.01  --bmc1_k_induction                      false
% 2.60/1.01  --bmc1_non_equiv_states                 false
% 2.60/1.01  --bmc1_deadlock                         false
% 2.60/1.01  --bmc1_ucm                              false
% 2.60/1.01  --bmc1_add_unsat_core                   none
% 2.60/1.01  --bmc1_unsat_core_children              false
% 2.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.01  --bmc1_out_stat                         full
% 2.60/1.01  --bmc1_ground_init                      false
% 2.60/1.01  --bmc1_pre_inst_next_state              false
% 2.60/1.01  --bmc1_pre_inst_state                   false
% 2.60/1.01  --bmc1_pre_inst_reach_state             false
% 2.60/1.01  --bmc1_out_unsat_core                   false
% 2.60/1.01  --bmc1_aig_witness_out                  false
% 2.60/1.01  --bmc1_verbose                          false
% 2.60/1.01  --bmc1_dump_clauses_tptp                false
% 2.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.01  --bmc1_dump_file                        -
% 2.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.01  --bmc1_ucm_extend_mode                  1
% 2.60/1.01  --bmc1_ucm_init_mode                    2
% 2.60/1.01  --bmc1_ucm_cone_mode                    none
% 2.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.01  --bmc1_ucm_relax_model                  4
% 2.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.01  --bmc1_ucm_layered_model                none
% 2.60/1.01  --bmc1_ucm_max_lemma_size               10
% 2.60/1.01  
% 2.60/1.01  ------ AIG Options
% 2.60/1.01  
% 2.60/1.01  --aig_mode                              false
% 2.60/1.01  
% 2.60/1.01  ------ Instantiation Options
% 2.60/1.01  
% 2.60/1.01  --instantiation_flag                    true
% 2.60/1.01  --inst_sos_flag                         false
% 2.60/1.01  --inst_sos_phase                        true
% 2.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.01  --inst_lit_sel_side                     num_symb
% 2.60/1.01  --inst_solver_per_active                1400
% 2.60/1.01  --inst_solver_calls_frac                1.
% 2.60/1.01  --inst_passive_queue_type               priority_queues
% 2.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.01  --inst_passive_queues_freq              [25;2]
% 2.60/1.01  --inst_dismatching                      true
% 2.60/1.01  --inst_eager_unprocessed_to_passive     true
% 2.60/1.01  --inst_prop_sim_given                   true
% 2.60/1.01  --inst_prop_sim_new                     false
% 2.60/1.01  --inst_subs_new                         false
% 2.60/1.01  --inst_eq_res_simp                      false
% 2.60/1.01  --inst_subs_given                       false
% 2.60/1.01  --inst_orphan_elimination               true
% 2.60/1.01  --inst_learning_loop_flag               true
% 2.60/1.01  --inst_learning_start                   3000
% 2.60/1.01  --inst_learning_factor                  2
% 2.60/1.01  --inst_start_prop_sim_after_learn       3
% 2.60/1.01  --inst_sel_renew                        solver
% 2.60/1.01  --inst_lit_activity_flag                true
% 2.60/1.01  --inst_restr_to_given                   false
% 2.60/1.01  --inst_activity_threshold               500
% 2.60/1.01  --inst_out_proof                        true
% 2.60/1.01  
% 2.60/1.01  ------ Resolution Options
% 2.60/1.01  
% 2.60/1.01  --resolution_flag                       true
% 2.60/1.01  --res_lit_sel                           adaptive
% 2.60/1.01  --res_lit_sel_side                      none
% 2.60/1.01  --res_ordering                          kbo
% 2.60/1.01  --res_to_prop_solver                    active
% 2.60/1.01  --res_prop_simpl_new                    false
% 2.60/1.01  --res_prop_simpl_given                  true
% 2.60/1.01  --res_passive_queue_type                priority_queues
% 2.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.01  --res_passive_queues_freq               [15;5]
% 2.60/1.01  --res_forward_subs                      full
% 2.60/1.01  --res_backward_subs                     full
% 2.60/1.01  --res_forward_subs_resolution           true
% 2.60/1.01  --res_backward_subs_resolution          true
% 2.60/1.01  --res_orphan_elimination                true
% 2.60/1.01  --res_time_limit                        2.
% 2.60/1.01  --res_out_proof                         true
% 2.60/1.01  
% 2.60/1.01  ------ Superposition Options
% 2.60/1.01  
% 2.60/1.01  --superposition_flag                    true
% 2.60/1.01  --sup_passive_queue_type                priority_queues
% 2.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.01  --demod_completeness_check              fast
% 2.60/1.01  --demod_use_ground                      true
% 2.60/1.01  --sup_to_prop_solver                    passive
% 2.60/1.01  --sup_prop_simpl_new                    true
% 2.60/1.01  --sup_prop_simpl_given                  true
% 2.60/1.01  --sup_fun_splitting                     false
% 2.60/1.01  --sup_smt_interval                      50000
% 2.60/1.01  
% 2.60/1.01  ------ Superposition Simplification Setup
% 2.60/1.01  
% 2.60/1.01  --sup_indices_passive                   []
% 2.60/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.01  --sup_full_bw                           [BwDemod]
% 2.60/1.01  --sup_immed_triv                        [TrivRules]
% 2.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.01  --sup_immed_bw_main                     []
% 2.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.01  
% 2.60/1.01  ------ Combination Options
% 2.60/1.01  
% 2.60/1.01  --comb_res_mult                         3
% 2.60/1.01  --comb_sup_mult                         2
% 2.60/1.01  --comb_inst_mult                        10
% 2.60/1.01  
% 2.60/1.01  ------ Debug Options
% 2.60/1.01  
% 2.60/1.01  --dbg_backtrace                         false
% 2.60/1.01  --dbg_dump_prop_clauses                 false
% 2.60/1.01  --dbg_dump_prop_clauses_file            -
% 2.60/1.01  --dbg_out_stat                          false
% 2.60/1.01  ------ Parsing...
% 2.60/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/1.01  ------ Proving...
% 2.60/1.01  ------ Problem Properties 
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  clauses                                 29
% 2.60/1.01  conjectures                             2
% 2.60/1.01  EPR                                     0
% 2.60/1.01  Horn                                    25
% 2.60/1.01  unary                                   11
% 2.60/1.01  binary                                  8
% 2.60/1.01  lits                                    63
% 2.60/1.01  lits eq                                 43
% 2.60/1.01  fd_pure                                 0
% 2.60/1.01  fd_pseudo                               0
% 2.60/1.01  fd_cond                                 1
% 2.60/1.01  fd_pseudo_cond                          0
% 2.60/1.01  AC symbols                              0
% 2.60/1.01  
% 2.60/1.01  ------ Schedule dynamic 5 is on 
% 2.60/1.01  
% 2.60/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  ------ 
% 2.60/1.01  Current options:
% 2.60/1.01  ------ 
% 2.60/1.01  
% 2.60/1.01  ------ Input Options
% 2.60/1.01  
% 2.60/1.01  --out_options                           all
% 2.60/1.01  --tptp_safe_out                         true
% 2.60/1.01  --problem_path                          ""
% 2.60/1.01  --include_path                          ""
% 2.60/1.01  --clausifier                            res/vclausify_rel
% 2.60/1.01  --clausifier_options                    --mode clausify
% 2.60/1.01  --stdin                                 false
% 2.60/1.01  --stats_out                             all
% 2.60/1.01  
% 2.60/1.01  ------ General Options
% 2.60/1.01  
% 2.60/1.01  --fof                                   false
% 2.60/1.01  --time_out_real                         305.
% 2.60/1.01  --time_out_virtual                      -1.
% 2.60/1.01  --symbol_type_check                     false
% 2.60/1.01  --clausify_out                          false
% 2.60/1.01  --sig_cnt_out                           false
% 2.60/1.01  --trig_cnt_out                          false
% 2.60/1.01  --trig_cnt_out_tolerance                1.
% 2.60/1.01  --trig_cnt_out_sk_spl                   false
% 2.60/1.01  --abstr_cl_out                          false
% 2.60/1.01  
% 2.60/1.01  ------ Global Options
% 2.60/1.01  
% 2.60/1.01  --schedule                              default
% 2.60/1.01  --add_important_lit                     false
% 2.60/1.01  --prop_solver_per_cl                    1000
% 2.60/1.01  --min_unsat_core                        false
% 2.60/1.01  --soft_assumptions                      false
% 2.60/1.01  --soft_lemma_size                       3
% 2.60/1.01  --prop_impl_unit_size                   0
% 2.60/1.01  --prop_impl_unit                        []
% 2.60/1.01  --share_sel_clauses                     true
% 2.60/1.01  --reset_solvers                         false
% 2.60/1.01  --bc_imp_inh                            [conj_cone]
% 2.60/1.01  --conj_cone_tolerance                   3.
% 2.60/1.01  --extra_neg_conj                        none
% 2.60/1.01  --large_theory_mode                     true
% 2.60/1.01  --prolific_symb_bound                   200
% 2.60/1.01  --lt_threshold                          2000
% 2.60/1.01  --clause_weak_htbl                      true
% 2.60/1.01  --gc_record_bc_elim                     false
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing Options
% 2.60/1.01  
% 2.60/1.01  --preprocessing_flag                    true
% 2.60/1.01  --time_out_prep_mult                    0.1
% 2.60/1.01  --splitting_mode                        input
% 2.60/1.01  --splitting_grd                         true
% 2.60/1.01  --splitting_cvd                         false
% 2.60/1.01  --splitting_cvd_svl                     false
% 2.60/1.01  --splitting_nvd                         32
% 2.60/1.01  --sub_typing                            true
% 2.60/1.01  --prep_gs_sim                           true
% 2.60/1.01  --prep_unflatten                        true
% 2.60/1.01  --prep_res_sim                          true
% 2.60/1.01  --prep_upred                            true
% 2.60/1.01  --prep_sem_filter                       exhaustive
% 2.60/1.01  --prep_sem_filter_out                   false
% 2.60/1.01  --pred_elim                             true
% 2.60/1.01  --res_sim_input                         true
% 2.60/1.01  --eq_ax_congr_red                       true
% 2.60/1.01  --pure_diseq_elim                       true
% 2.60/1.01  --brand_transform                       false
% 2.60/1.01  --non_eq_to_eq                          false
% 2.60/1.01  --prep_def_merge                        true
% 2.60/1.01  --prep_def_merge_prop_impl              false
% 2.60/1.01  --prep_def_merge_mbd                    true
% 2.60/1.01  --prep_def_merge_tr_red                 false
% 2.60/1.01  --prep_def_merge_tr_cl                  false
% 2.60/1.01  --smt_preprocessing                     true
% 2.60/1.01  --smt_ac_axioms                         fast
% 2.60/1.01  --preprocessed_out                      false
% 2.60/1.01  --preprocessed_stats                    false
% 2.60/1.01  
% 2.60/1.01  ------ Abstraction refinement Options
% 2.60/1.01  
% 2.60/1.01  --abstr_ref                             []
% 2.60/1.01  --abstr_ref_prep                        false
% 2.60/1.01  --abstr_ref_until_sat                   false
% 2.60/1.01  --abstr_ref_sig_restrict                funpre
% 2.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.01  --abstr_ref_under                       []
% 2.60/1.01  
% 2.60/1.01  ------ SAT Options
% 2.60/1.01  
% 2.60/1.01  --sat_mode                              false
% 2.60/1.01  --sat_fm_restart_options                ""
% 2.60/1.01  --sat_gr_def                            false
% 2.60/1.01  --sat_epr_types                         true
% 2.60/1.01  --sat_non_cyclic_types                  false
% 2.60/1.01  --sat_finite_models                     false
% 2.60/1.01  --sat_fm_lemmas                         false
% 2.60/1.01  --sat_fm_prep                           false
% 2.60/1.01  --sat_fm_uc_incr                        true
% 2.60/1.01  --sat_out_model                         small
% 2.60/1.01  --sat_out_clauses                       false
% 2.60/1.01  
% 2.60/1.01  ------ QBF Options
% 2.60/1.01  
% 2.60/1.01  --qbf_mode                              false
% 2.60/1.01  --qbf_elim_univ                         false
% 2.60/1.01  --qbf_dom_inst                          none
% 2.60/1.01  --qbf_dom_pre_inst                      false
% 2.60/1.01  --qbf_sk_in                             false
% 2.60/1.01  --qbf_pred_elim                         true
% 2.60/1.01  --qbf_split                             512
% 2.60/1.01  
% 2.60/1.01  ------ BMC1 Options
% 2.60/1.01  
% 2.60/1.01  --bmc1_incremental                      false
% 2.60/1.01  --bmc1_axioms                           reachable_all
% 2.60/1.01  --bmc1_min_bound                        0
% 2.60/1.01  --bmc1_max_bound                        -1
% 2.60/1.01  --bmc1_max_bound_default                -1
% 2.60/1.01  --bmc1_symbol_reachability              true
% 2.60/1.01  --bmc1_property_lemmas                  false
% 2.60/1.01  --bmc1_k_induction                      false
% 2.60/1.01  --bmc1_non_equiv_states                 false
% 2.60/1.01  --bmc1_deadlock                         false
% 2.60/1.01  --bmc1_ucm                              false
% 2.60/1.01  --bmc1_add_unsat_core                   none
% 2.60/1.01  --bmc1_unsat_core_children              false
% 2.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.01  --bmc1_out_stat                         full
% 2.60/1.01  --bmc1_ground_init                      false
% 2.60/1.01  --bmc1_pre_inst_next_state              false
% 2.60/1.01  --bmc1_pre_inst_state                   false
% 2.60/1.01  --bmc1_pre_inst_reach_state             false
% 2.60/1.01  --bmc1_out_unsat_core                   false
% 2.60/1.01  --bmc1_aig_witness_out                  false
% 2.60/1.01  --bmc1_verbose                          false
% 2.60/1.01  --bmc1_dump_clauses_tptp                false
% 2.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.01  --bmc1_dump_file                        -
% 2.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.01  --bmc1_ucm_extend_mode                  1
% 2.60/1.01  --bmc1_ucm_init_mode                    2
% 2.60/1.01  --bmc1_ucm_cone_mode                    none
% 2.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.01  --bmc1_ucm_relax_model                  4
% 2.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.01  --bmc1_ucm_layered_model                none
% 2.60/1.01  --bmc1_ucm_max_lemma_size               10
% 2.60/1.01  
% 2.60/1.01  ------ AIG Options
% 2.60/1.01  
% 2.60/1.01  --aig_mode                              false
% 2.60/1.01  
% 2.60/1.01  ------ Instantiation Options
% 2.60/1.01  
% 2.60/1.01  --instantiation_flag                    true
% 2.60/1.01  --inst_sos_flag                         false
% 2.60/1.01  --inst_sos_phase                        true
% 2.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.01  --inst_lit_sel_side                     none
% 2.60/1.01  --inst_solver_per_active                1400
% 2.60/1.01  --inst_solver_calls_frac                1.
% 2.60/1.01  --inst_passive_queue_type               priority_queues
% 2.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.01  --inst_passive_queues_freq              [25;2]
% 2.60/1.01  --inst_dismatching                      true
% 2.60/1.01  --inst_eager_unprocessed_to_passive     true
% 2.60/1.01  --inst_prop_sim_given                   true
% 2.60/1.01  --inst_prop_sim_new                     false
% 2.60/1.01  --inst_subs_new                         false
% 2.60/1.01  --inst_eq_res_simp                      false
% 2.60/1.01  --inst_subs_given                       false
% 2.60/1.01  --inst_orphan_elimination               true
% 2.60/1.01  --inst_learning_loop_flag               true
% 2.60/1.01  --inst_learning_start                   3000
% 2.60/1.01  --inst_learning_factor                  2
% 2.60/1.01  --inst_start_prop_sim_after_learn       3
% 2.60/1.01  --inst_sel_renew                        solver
% 2.60/1.01  --inst_lit_activity_flag                true
% 2.60/1.01  --inst_restr_to_given                   false
% 2.60/1.01  --inst_activity_threshold               500
% 2.60/1.01  --inst_out_proof                        true
% 2.60/1.01  
% 2.60/1.01  ------ Resolution Options
% 2.60/1.01  
% 2.60/1.01  --resolution_flag                       false
% 2.60/1.01  --res_lit_sel                           adaptive
% 2.60/1.01  --res_lit_sel_side                      none
% 2.60/1.01  --res_ordering                          kbo
% 2.60/1.01  --res_to_prop_solver                    active
% 2.60/1.01  --res_prop_simpl_new                    false
% 2.60/1.01  --res_prop_simpl_given                  true
% 2.60/1.01  --res_passive_queue_type                priority_queues
% 2.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.01  --res_passive_queues_freq               [15;5]
% 2.60/1.01  --res_forward_subs                      full
% 2.60/1.01  --res_backward_subs                     full
% 2.60/1.01  --res_forward_subs_resolution           true
% 2.60/1.01  --res_backward_subs_resolution          true
% 2.60/1.01  --res_orphan_elimination                true
% 2.60/1.01  --res_time_limit                        2.
% 2.60/1.01  --res_out_proof                         true
% 2.60/1.01  
% 2.60/1.01  ------ Superposition Options
% 2.60/1.01  
% 2.60/1.01  --superposition_flag                    true
% 2.60/1.01  --sup_passive_queue_type                priority_queues
% 2.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.01  --demod_completeness_check              fast
% 2.60/1.01  --demod_use_ground                      true
% 2.60/1.01  --sup_to_prop_solver                    passive
% 2.60/1.01  --sup_prop_simpl_new                    true
% 2.60/1.01  --sup_prop_simpl_given                  true
% 2.60/1.01  --sup_fun_splitting                     false
% 2.60/1.01  --sup_smt_interval                      50000
% 2.60/1.01  
% 2.60/1.01  ------ Superposition Simplification Setup
% 2.60/1.01  
% 2.60/1.01  --sup_indices_passive                   []
% 2.60/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.01  --sup_full_bw                           [BwDemod]
% 2.60/1.01  --sup_immed_triv                        [TrivRules]
% 2.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.01  --sup_immed_bw_main                     []
% 2.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.01  
% 2.60/1.01  ------ Combination Options
% 2.60/1.01  
% 2.60/1.01  --comb_res_mult                         3
% 2.60/1.01  --comb_sup_mult                         2
% 2.60/1.01  --comb_inst_mult                        10
% 2.60/1.01  
% 2.60/1.01  ------ Debug Options
% 2.60/1.01  
% 2.60/1.01  --dbg_backtrace                         false
% 2.60/1.01  --dbg_dump_prop_clauses                 false
% 2.60/1.01  --dbg_dump_prop_clauses_file            -
% 2.60/1.01  --dbg_out_stat                          false
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  ------ Proving...
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  % SZS status Theorem for theBenchmark.p
% 2.60/1.01  
% 2.60/1.01   Resolution empty clause
% 2.60/1.01  
% 2.60/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.01  
% 2.60/1.01  fof(f2,axiom,(
% 2.60/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f50,plain,(
% 2.60/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.60/1.01    inference(cnf_transformation,[],[f2])).
% 2.60/1.01  
% 2.60/1.01  fof(f13,axiom,(
% 2.60/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f29,plain,(
% 2.60/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.01    inference(ennf_transformation,[],[f13])).
% 2.60/1.01  
% 2.60/1.01  fof(f62,plain,(
% 2.60/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.01    inference(cnf_transformation,[],[f29])).
% 2.60/1.01  
% 2.60/1.01  fof(f15,axiom,(
% 2.60/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f31,plain,(
% 2.60/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.60/1.01    inference(ennf_transformation,[],[f15])).
% 2.60/1.01  
% 2.60/1.01  fof(f32,plain,(
% 2.60/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.60/1.01    inference(flattening,[],[f31])).
% 2.60/1.01  
% 2.60/1.01  fof(f42,plain,(
% 2.60/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.60/1.01    inference(nnf_transformation,[],[f32])).
% 2.60/1.01  
% 2.60/1.01  fof(f65,plain,(
% 2.60/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f42])).
% 2.60/1.01  
% 2.60/1.01  fof(f17,axiom,(
% 2.60/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f33,plain,(
% 2.60/1.01    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.60/1.01    inference(ennf_transformation,[],[f17])).
% 2.60/1.01  
% 2.60/1.01  fof(f34,plain,(
% 2.60/1.01    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.60/1.01    inference(flattening,[],[f33])).
% 2.60/1.01  
% 2.60/1.01  fof(f68,plain,(
% 2.60/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f34])).
% 2.60/1.01  
% 2.60/1.01  fof(f20,conjecture,(
% 2.60/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f21,negated_conjecture,(
% 2.60/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.60/1.01    inference(negated_conjecture,[],[f20])).
% 2.60/1.01  
% 2.60/1.01  fof(f37,plain,(
% 2.60/1.01    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.60/1.01    inference(ennf_transformation,[],[f21])).
% 2.60/1.01  
% 2.60/1.01  fof(f38,plain,(
% 2.60/1.01    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.60/1.01    inference(flattening,[],[f37])).
% 2.60/1.01  
% 2.60/1.01  fof(f45,plain,(
% 2.60/1.01    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.60/1.01    introduced(choice_axiom,[])).
% 2.60/1.01  
% 2.60/1.01  fof(f44,plain,(
% 2.60/1.01    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 2.60/1.01    introduced(choice_axiom,[])).
% 2.60/1.01  
% 2.60/1.01  fof(f43,plain,(
% 2.60/1.01    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.60/1.01    introduced(choice_axiom,[])).
% 2.60/1.01  
% 2.60/1.01  fof(f46,plain,(
% 2.60/1.01    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f45,f44,f43])).
% 2.60/1.01  
% 2.60/1.01  fof(f75,plain,(
% 2.60/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.60/1.01    inference(cnf_transformation,[],[f46])).
% 2.60/1.01  
% 2.60/1.01  fof(f74,plain,(
% 2.60/1.01    v1_funct_1(sK2)),
% 2.60/1.01    inference(cnf_transformation,[],[f46])).
% 2.60/1.01  
% 2.60/1.01  fof(f76,plain,(
% 2.60/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.60/1.01    inference(cnf_transformation,[],[f46])).
% 2.60/1.01  
% 2.60/1.01  fof(f19,axiom,(
% 2.60/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f36,plain,(
% 2.60/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.60/1.01    inference(ennf_transformation,[],[f19])).
% 2.60/1.01  
% 2.60/1.01  fof(f71,plain,(
% 2.60/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f36])).
% 2.60/1.01  
% 2.60/1.01  fof(f73,plain,(
% 2.60/1.01    l1_struct_0(sK1)),
% 2.60/1.01    inference(cnf_transformation,[],[f46])).
% 2.60/1.01  
% 2.60/1.01  fof(f72,plain,(
% 2.60/1.01    l1_struct_0(sK0)),
% 2.60/1.01    inference(cnf_transformation,[],[f46])).
% 2.60/1.01  
% 2.60/1.01  fof(f4,axiom,(
% 2.60/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f24,plain,(
% 2.60/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.60/1.01    inference(ennf_transformation,[],[f4])).
% 2.60/1.01  
% 2.60/1.01  fof(f51,plain,(
% 2.60/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f24])).
% 2.60/1.01  
% 2.60/1.01  fof(f6,axiom,(
% 2.60/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f54,plain,(
% 2.60/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.60/1.01    inference(cnf_transformation,[],[f6])).
% 2.60/1.01  
% 2.60/1.01  fof(f77,plain,(
% 2.60/1.01    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 2.60/1.01    inference(cnf_transformation,[],[f46])).
% 2.60/1.01  
% 2.60/1.01  fof(f63,plain,(
% 2.60/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.01    inference(cnf_transformation,[],[f29])).
% 2.60/1.01  
% 2.60/1.01  fof(f5,axiom,(
% 2.60/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f25,plain,(
% 2.60/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.60/1.01    inference(ennf_transformation,[],[f5])).
% 2.60/1.01  
% 2.60/1.01  fof(f41,plain,(
% 2.60/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.60/1.01    inference(nnf_transformation,[],[f25])).
% 2.60/1.01  
% 2.60/1.01  fof(f52,plain,(
% 2.60/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f41])).
% 2.60/1.01  
% 2.60/1.01  fof(f10,axiom,(
% 2.60/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f27,plain,(
% 2.60/1.01    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.60/1.01    inference(ennf_transformation,[],[f10])).
% 2.60/1.01  
% 2.60/1.01  fof(f28,plain,(
% 2.60/1.01    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.60/1.01    inference(flattening,[],[f27])).
% 2.60/1.01  
% 2.60/1.01  fof(f59,plain,(
% 2.60/1.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f28])).
% 2.60/1.01  
% 2.60/1.01  fof(f16,axiom,(
% 2.60/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f67,plain,(
% 2.60/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f16])).
% 2.60/1.01  
% 2.60/1.01  fof(f81,plain,(
% 2.60/1.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.60/1.01    inference(definition_unfolding,[],[f59,f67])).
% 2.60/1.01  
% 2.60/1.01  fof(f12,axiom,(
% 2.60/1.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f22,plain,(
% 2.60/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.60/1.01    inference(pure_predicate_removal,[],[f12])).
% 2.60/1.01  
% 2.60/1.01  fof(f61,plain,(
% 2.60/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.60/1.01    inference(cnf_transformation,[],[f22])).
% 2.60/1.01  
% 2.60/1.01  fof(f83,plain,(
% 2.60/1.01    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.60/1.01    inference(definition_unfolding,[],[f61,f67])).
% 2.60/1.01  
% 2.60/1.01  fof(f8,axiom,(
% 2.60/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f26,plain,(
% 2.60/1.01    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.60/1.01    inference(ennf_transformation,[],[f8])).
% 2.60/1.01  
% 2.60/1.01  fof(f56,plain,(
% 2.60/1.01    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f26])).
% 2.60/1.01  
% 2.60/1.01  fof(f9,axiom,(
% 2.60/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f57,plain,(
% 2.60/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.60/1.01    inference(cnf_transformation,[],[f9])).
% 2.60/1.01  
% 2.60/1.01  fof(f80,plain,(
% 2.60/1.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.60/1.01    inference(definition_unfolding,[],[f57,f67])).
% 2.60/1.01  
% 2.60/1.01  fof(f14,axiom,(
% 2.60/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f30,plain,(
% 2.60/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.01    inference(ennf_transformation,[],[f14])).
% 2.60/1.01  
% 2.60/1.01  fof(f64,plain,(
% 2.60/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.01    inference(cnf_transformation,[],[f30])).
% 2.60/1.01  
% 2.60/1.01  fof(f78,plain,(
% 2.60/1.01    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 2.60/1.01    inference(cnf_transformation,[],[f46])).
% 2.60/1.01  
% 2.60/1.01  fof(f69,plain,(
% 2.60/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.60/1.01    inference(cnf_transformation,[],[f34])).
% 2.60/1.01  
% 2.60/1.01  fof(f87,plain,(
% 2.60/1.01    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 2.60/1.01    inference(equality_resolution,[],[f69])).
% 2.60/1.01  
% 2.60/1.01  fof(f1,axiom,(
% 2.60/1.01    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.01  
% 2.60/1.01  fof(f39,plain,(
% 2.60/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.60/1.01    inference(nnf_transformation,[],[f1])).
% 2.60/1.01  
% 2.60/1.01  fof(f40,plain,(
% 2.60/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.60/1.01    inference(flattening,[],[f39])).
% 2.60/1.01  
% 2.60/1.01  fof(f48,plain,(
% 2.60/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.60/1.01    inference(cnf_transformation,[],[f40])).
% 2.60/1.01  
% 2.60/1.01  fof(f85,plain,(
% 2.60/1.01    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.60/1.01    inference(equality_resolution,[],[f48])).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3,plain,
% 2.60/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.60/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_16,plain,
% 2.60/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_19,plain,
% 2.60/1.01      ( ~ v1_partfun1(X0,X1)
% 2.60/1.01      | ~ v4_relat_1(X0,X1)
% 2.60/1.01      | ~ v1_relat_1(X0)
% 2.60/1.01      | k1_relat_1(X0) = X1 ),
% 2.60/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_21,plain,
% 2.60/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.60/1.01      | v1_partfun1(X0,X1)
% 2.60/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.01      | ~ v1_funct_1(X0)
% 2.60/1.01      | k1_xboole_0 = X2 ),
% 2.60/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_27,negated_conjecture,
% 2.60/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.60/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_375,plain,
% 2.60/1.01      ( v1_partfun1(X0,X1)
% 2.60/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.01      | ~ v1_funct_1(X0)
% 2.60/1.01      | u1_struct_0(sK1) != X2
% 2.60/1.01      | u1_struct_0(sK0) != X1
% 2.60/1.01      | sK2 != X0
% 2.60/1.01      | k1_xboole_0 = X2 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_376,plain,
% 2.60/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.60/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.60/1.01      | ~ v1_funct_1(sK2)
% 2.60/1.01      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_375]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_28,negated_conjecture,
% 2.60/1.01      ( v1_funct_1(sK2) ),
% 2.60/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_26,negated_conjecture,
% 2.60/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_378,plain,
% 2.60/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_376,c_28,c_26]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_417,plain,
% 2.60/1.01      ( ~ v4_relat_1(X0,X1)
% 2.60/1.01      | ~ v1_relat_1(X0)
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) != X1
% 2.60/1.01      | k1_relat_1(X0) = X1
% 2.60/1.01      | sK2 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_378]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_418,plain,
% 2.60/1.01      ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
% 2.60/1.01      | ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_417]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_443,plain,
% 2.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.01      | ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) != X1
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | sK2 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_418]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_444,plain,
% 2.60/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.60/1.01      | ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_443]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_532,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) != k1_zfmisc_1(X1)
% 2.60/1.01      | sK2 != k1_xboole_0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_444]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_773,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | sP1_iProver_split
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | sK2 != k1_xboole_0 ),
% 2.60/1.01      inference(splitting,
% 2.60/1.01                [splitting(split),new_symbols(definition,[])],
% 2.60/1.01                [c_532]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1029,plain,
% 2.60/1.01      ( u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | sK2 != k1_xboole_0
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top
% 2.60/1.01      | sP1_iProver_split = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_23,plain,
% 2.60/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_29,negated_conjecture,
% 2.60/1.01      ( l1_struct_0(sK1) ),
% 2.60/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_270,plain,
% 2.60/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_271,plain,
% 2.60/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_270]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_30,negated_conjecture,
% 2.60/1.01      ( l1_struct_0(sK0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_275,plain,
% 2.60/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_276,plain,
% 2.60/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_275]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1147,plain,
% 2.60/1.01      ( k2_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | sK2 != k1_xboole_0
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top
% 2.60/1.01      | sP1_iProver_split = iProver_top ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1029,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_618,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
% 2.60/1.01      | sK2 != sK2 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_444]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_697,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_618]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_771,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | sP0_iProver_split
% 2.60/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.60/1.01      inference(splitting,
% 2.60/1.01                [splitting(split),new_symbols(definition,[])],
% 2.60/1.01                [c_697]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1025,plain,
% 2.60/1.01      ( u1_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top
% 2.60/1.01      | sP0_iProver_split = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1107,plain,
% 2.60/1.01      ( k2_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top
% 2.60/1.01      | sP0_iProver_split = iProver_top ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1025,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1184,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | sP0_iProver_split
% 2.60/1.01      | k2_struct_0(sK1) = k1_xboole_0
% 2.60/1.01      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.60/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1107]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_777,plain,( X0 = X0 ),theory(equality) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1231,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.60/1.01      inference(instantiation,[status(thm)],[c_777]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_770,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
% 2.60/1.01      | ~ sP0_iProver_split ),
% 2.60/1.01      inference(splitting,
% 2.60/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.60/1.01                [c_697]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1026,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
% 2.60/1.01      | sP0_iProver_split != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1092,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))
% 2.60/1.01      | sP0_iProver_split != iProver_top ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_1026,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1271,plain,
% 2.60/1.01      ( sP0_iProver_split != iProver_top ),
% 2.60/1.01      inference(equality_resolution,[status(thm)],[c_1092]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1272,plain,
% 2.60/1.01      ( ~ sP0_iProver_split ),
% 2.60/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1271]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4,plain,
% 2.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_561,plain,
% 2.60/1.01      ( ~ v1_relat_1(X0)
% 2.60/1.01      | v1_relat_1(X1)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.60/1.01      | sK2 != X1 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_562,plain,
% 2.60/1.01      ( ~ v1_relat_1(X0)
% 2.60/1.01      | v1_relat_1(sK2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_561]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1224,plain,
% 2.60/1.01      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.60/1.01      | v1_relat_1(sK2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.60/1.01      inference(instantiation,[status(thm)],[c_562]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1341,plain,
% 2.60/1.01      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.60/1.01      | v1_relat_1(sK2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.60/1.01      inference(instantiation,[status(thm)],[c_1224]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_7,plain,
% 2.60/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.60/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1487,plain,
% 2.60/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.60/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1534,plain,
% 2.60/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1147,c_1184,c_1231,c_1272,c_1341,c_1487]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1535,plain,
% 2.60/1.01      ( k2_struct_0(sK1) = k1_xboole_0 | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_1534]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_25,negated_conjecture,
% 2.60/1.01      ( k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1545,plain,
% 2.60/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1535,c_25]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_15,plain,
% 2.60/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6,plain,
% 2.60/1.01      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_282,plain,
% 2.60/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 2.60/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.60/1.01      | ~ v1_relat_1(X0) ),
% 2.60/1.01      inference(resolution,[status(thm)],[c_15,c_6]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_12,plain,
% 2.60/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.60/1.01      | ~ v1_relat_1(X0)
% 2.60/1.01      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 2.60/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_301,plain,
% 2.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.01      | ~ v1_relat_1(X0)
% 2.60/1.01      | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
% 2.60/1.01      inference(resolution,[status(thm)],[c_282,c_12]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_576,plain,
% 2.60/1.01      ( ~ v1_relat_1(X0)
% 2.60/1.01      | k5_relat_1(X0,k6_partfun1(X1)) = X0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 2.60/1.01      | sK2 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_301,c_26]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_577,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | k5_relat_1(sK2,k6_partfun1(X0)) = sK2
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_576]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1027,plain,
% 2.60/1.01      ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1140,plain,
% 2.60/1.01      ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_1027,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1440,plain,
% 2.60/1.01      ( k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.60/1.01      inference(equality_resolution,[status(thm)],[c_1140]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1454,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2 ),
% 2.60/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1440]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2535,plain,
% 2.60/1.01      ( k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2 ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1440,c_1231,c_1341,c_1454,c_1487]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_14,plain,
% 2.60/1.01      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.60/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1035,plain,
% 2.60/1.01      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1028,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.60/1.01      | v1_relat_1(X0) != iProver_top
% 2.60/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1116,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.60/1.01      | v1_relat_1(X0) != iProver_top
% 2.60/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_1028,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1598,plain,
% 2.60/1.01      ( k2_struct_0(sK0) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.60/1.01      | v1_relat_1(X0) != iProver_top
% 2.60/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1545,c_1116]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1342,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.60/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.60/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_1341]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1488,plain,
% 2.60/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1943,plain,
% 2.60/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1598,c_1231,c_1342,c_1488]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_9,plain,
% 2.60/1.01      ( ~ v1_relat_1(X0)
% 2.60/1.01      | ~ v1_relat_1(X1)
% 2.60/1.01      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
% 2.60/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1036,plain,
% 2.60/1.01      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 2.60/1.01      | v1_relat_1(X0) != iProver_top
% 2.60/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2859,plain,
% 2.60/1.01      ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
% 2.60/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1943,c_1036]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3067,plain,
% 2.60/1.01      ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_partfun1(X0))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1035,c_2859]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_11,plain,
% 2.60/1.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.60/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3076,plain,
% 2.60/1.01      ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,X0) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_3067,c_11]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3475,plain,
% 2.60/1.01      ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2535,c_3076]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_17,plain,
% 2.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.60/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_591,plain,
% 2.60/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.60/1.01      | sK2 != X2 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_592,plain,
% 2.60/1.01      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_591]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1135,plain,
% 2.60/1.01      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_592,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1390,plain,
% 2.60/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.60/1.01      inference(equality_resolution,[status(thm)],[c_1135]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_24,negated_conjecture,
% 2.60/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1062,plain,
% 2.60/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_24,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2472,plain,
% 2.60/1.01      ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1390,c_1062]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3767,plain,
% 2.60/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_3475,c_2472]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3770,plain,
% 2.60/1.01      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1545,c_3767]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3810,plain,
% 2.60/1.01      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_3770,c_3767]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_20,plain,
% 2.60/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.60/1.01      | v1_partfun1(X0,k1_xboole_0)
% 2.60/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.60/1.01      | ~ v1_funct_1(X0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_358,plain,
% 2.60/1.01      ( v1_partfun1(X0,k1_xboole_0)
% 2.60/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.60/1.01      | ~ v1_funct_1(X0)
% 2.60/1.01      | u1_struct_0(sK1) != X1
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | sK2 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_359,plain,
% 2.60/1.01      ( v1_partfun1(sK2,k1_xboole_0)
% 2.60/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.60/1.01      | ~ v1_funct_1(sK2)
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0 ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_358]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_361,plain,
% 2.60/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.60/1.01      | v1_partfun1(sK2,k1_xboole_0)
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0 ),
% 2.60/1.01      inference(global_propositional_subsumption,[status(thm)],[c_359,c_28]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_362,plain,
% 2.60/1.01      ( v1_partfun1(sK2,k1_xboole_0)
% 2.60/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0 ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_361]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_398,plain,
% 2.60/1.01      ( ~ v4_relat_1(X0,X1)
% 2.60/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.60/1.01      | ~ v1_relat_1(X0)
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(X0) = X1
% 2.60/1.01      | sK2 != X0
% 2.60/1.01      | k1_xboole_0 != X1 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_362]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_399,plain,
% 2.60/1.01      ( ~ v4_relat_1(sK2,k1_xboole_0)
% 2.60/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.60/1.01      | ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_398]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_411,plain,
% 2.60/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.60/1.01      | ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.60/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_399,c_16]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_600,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 2.60/1.01      | sK2 != sK2 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_411]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_701,plain,
% 2.60/1.01      ( ~ v1_relat_1(sK2)
% 2.60/1.01      | u1_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_600]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1024,plain,
% 2.60/1.01      ( u1_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1169,plain,
% 2.60/1.01      ( k2_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_1024,c_271,c_276]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1,plain,
% 2.60/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.60/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1170,plain,
% 2.60/1.01      ( k2_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
% 2.60/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1169,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3195,plain,
% 2.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k2_struct_0(sK0) != k1_xboole_0 ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1170,c_1231,c_1342,c_1488]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3196,plain,
% 2.60/1.01      ( k2_struct_0(sK0) != k1_xboole_0
% 2.60/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_3195]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3816,plain,
% 2.60/1.01      ( k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
% 2.60/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_3770,c_3196]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3902,plain,
% 2.60/1.01      ( k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_3816]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3905,plain,
% 2.60/1.01      ( k1_relat_1(sK2) = k1_xboole_0
% 2.60/1.01      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_3902,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3906,plain,
% 2.60/1.01      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_3905]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3909,plain,
% 2.60/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_3810,c_3906]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3910,plain,
% 2.60/1.01      ( $false ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_3909]) ).
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.01  
% 2.60/1.01  ------                               Statistics
% 2.60/1.01  
% 2.60/1.01  ------ General
% 2.60/1.01  
% 2.60/1.01  abstr_ref_over_cycles:                  0
% 2.60/1.01  abstr_ref_under_cycles:                 0
% 2.60/1.01  gc_basic_clause_elim:                   0
% 2.60/1.01  forced_gc_time:                         0
% 2.60/1.01  parsing_time:                           0.01
% 2.60/1.01  unif_index_cands_time:                  0.
% 2.60/1.01  unif_index_add_time:                    0.
% 2.60/1.01  orderings_time:                         0.
% 2.60/1.01  out_proof_time:                         0.009
% 2.60/1.01  total_time:                             0.156
% 2.60/1.01  num_of_symbols:                         57
% 2.60/1.01  num_of_terms:                           3267
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing
% 2.60/1.01  
% 2.60/1.01  num_of_splits:                          3
% 2.60/1.01  num_of_split_atoms:                     3
% 2.60/1.01  num_of_reused_defs:                     0
% 2.60/1.01  num_eq_ax_congr_red:                    6
% 2.60/1.01  num_of_sem_filtered_clauses:            1
% 2.60/1.01  num_of_subtypes:                        0
% 2.60/1.01  monotx_restored_types:                  0
% 2.60/1.01  sat_num_of_epr_types:                   0
% 2.60/1.01  sat_num_of_non_cyclic_types:            0
% 2.60/1.01  sat_guarded_non_collapsed_types:        0
% 2.60/1.01  num_pure_diseq_elim:                    0
% 2.60/1.01  simp_replaced_by:                       0
% 2.60/1.01  res_preprocessed:                       142
% 2.60/1.01  prep_upred:                             0
% 2.60/1.01  prep_unflattend:                        25
% 2.60/1.01  smt_new_axioms:                         0
% 2.60/1.01  pred_elim_cands:                        1
% 2.60/1.01  pred_elim:                              8
% 2.60/1.01  pred_elim_cl:                           5
% 2.60/1.01  pred_elim_cycles:                       11
% 2.60/1.01  merged_defs:                            0
% 2.60/1.01  merged_defs_ncl:                        0
% 2.60/1.01  bin_hyper_res:                          0
% 2.60/1.01  prep_cycles:                            4
% 2.60/1.01  pred_elim_time:                         0.009
% 2.60/1.01  splitting_time:                         0.
% 2.60/1.01  sem_filter_time:                        0.
% 2.60/1.01  monotx_time:                            0.
% 2.60/1.01  subtype_inf_time:                       0.
% 2.60/1.01  
% 2.60/1.01  ------ Problem properties
% 2.60/1.01  
% 2.60/1.01  clauses:                                29
% 2.60/1.01  conjectures:                            2
% 2.60/1.01  epr:                                    0
% 2.60/1.01  horn:                                   25
% 2.60/1.01  ground:                                 9
% 2.60/1.01  unary:                                  11
% 2.60/1.01  binary:                                 8
% 2.60/1.01  lits:                                   63
% 2.60/1.01  lits_eq:                                43
% 2.60/1.01  fd_pure:                                0
% 2.60/1.01  fd_pseudo:                              0
% 2.60/1.01  fd_cond:                                1
% 2.60/1.01  fd_pseudo_cond:                         0
% 2.60/1.01  ac_symbols:                             0
% 2.60/1.01  
% 2.60/1.01  ------ Propositional Solver
% 2.60/1.01  
% 2.60/1.01  prop_solver_calls:                      28
% 2.60/1.01  prop_fast_solver_calls:                 863
% 2.60/1.01  smt_solver_calls:                       0
% 2.60/1.01  smt_fast_solver_calls:                  0
% 2.60/1.01  prop_num_of_clauses:                    1345
% 2.60/1.01  prop_preprocess_simplified:             5066
% 2.60/1.01  prop_fo_subsumed:                       21
% 2.60/1.01  prop_solver_time:                       0.
% 2.60/1.01  smt_solver_time:                        0.
% 2.60/1.01  smt_fast_solver_time:                   0.
% 2.60/1.01  prop_fast_solver_time:                  0.
% 2.60/1.01  prop_unsat_core_time:                   0.
% 2.60/1.01  
% 2.60/1.01  ------ QBF
% 2.60/1.01  
% 2.60/1.01  qbf_q_res:                              0
% 2.60/1.01  qbf_num_tautologies:                    0
% 2.60/1.01  qbf_prep_cycles:                        0
% 2.60/1.01  
% 2.60/1.01  ------ BMC1
% 2.60/1.01  
% 2.60/1.01  bmc1_current_bound:                     -1
% 2.60/1.01  bmc1_last_solved_bound:                 -1
% 2.60/1.01  bmc1_unsat_core_size:                   -1
% 2.60/1.01  bmc1_unsat_core_parents_size:           -1
% 2.60/1.01  bmc1_merge_next_fun:                    0
% 2.60/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.60/1.01  
% 2.60/1.01  ------ Instantiation
% 2.60/1.01  
% 2.60/1.01  inst_num_of_clauses:                    720
% 2.60/1.01  inst_num_in_passive:                    411
% 2.60/1.01  inst_num_in_active:                     306
% 2.60/1.01  inst_num_in_unprocessed:                3
% 2.60/1.01  inst_num_of_loops:                      340
% 2.60/1.01  inst_num_of_learning_restarts:          0
% 2.60/1.01  inst_num_moves_active_passive:          31
% 2.60/1.01  inst_lit_activity:                      0
% 2.60/1.01  inst_lit_activity_moves:                0
% 2.60/1.01  inst_num_tautologies:                   0
% 2.60/1.01  inst_num_prop_implied:                  0
% 2.60/1.01  inst_num_existing_simplified:           0
% 2.60/1.01  inst_num_eq_res_simplified:             0
% 2.60/1.01  inst_num_child_elim:                    0
% 2.60/1.01  inst_num_of_dismatching_blockings:      98
% 2.60/1.01  inst_num_of_non_proper_insts:           552
% 2.60/1.01  inst_num_of_duplicates:                 0
% 2.60/1.01  inst_inst_num_from_inst_to_res:         0
% 2.60/1.01  inst_dismatching_checking_time:         0.
% 2.60/1.01  
% 2.60/1.01  ------ Resolution
% 2.60/1.01  
% 2.60/1.01  res_num_of_clauses:                     0
% 2.60/1.01  res_num_in_passive:                     0
% 2.60/1.01  res_num_in_active:                      0
% 2.60/1.01  res_num_of_loops:                       146
% 2.60/1.01  res_forward_subset_subsumed:            80
% 2.60/1.01  res_backward_subset_subsumed:           6
% 2.60/1.01  res_forward_subsumed:                   0
% 2.60/1.01  res_backward_subsumed:                  0
% 2.60/1.01  res_forward_subsumption_resolution:     1
% 2.60/1.01  res_backward_subsumption_resolution:    0
% 2.60/1.01  res_clause_to_clause_subsumption:       131
% 2.60/1.01  res_orphan_elimination:                 0
% 2.60/1.01  res_tautology_del:                      68
% 2.60/1.01  res_num_eq_res_simplified:              2
% 2.60/1.01  res_num_sel_changes:                    0
% 2.60/1.01  res_moves_from_active_to_pass:          0
% 2.60/1.01  
% 2.60/1.01  ------ Superposition
% 2.60/1.01  
% 2.60/1.01  sup_time_total:                         0.
% 2.60/1.01  sup_time_generating:                    0.
% 2.60/1.01  sup_time_sim_full:                      0.
% 2.60/1.01  sup_time_sim_immed:                     0.
% 2.60/1.01  
% 2.60/1.01  sup_num_of_clauses:                     47
% 2.60/1.01  sup_num_in_active:                      29
% 2.60/1.01  sup_num_in_passive:                     18
% 2.60/1.01  sup_num_of_loops:                       66
% 2.60/1.01  sup_fw_superposition:                   69
% 2.60/1.01  sup_bw_superposition:                   19
% 2.60/1.01  sup_immediate_simplified:               38
% 2.60/1.01  sup_given_eliminated:                   0
% 2.60/1.01  comparisons_done:                       0
% 2.60/1.01  comparisons_avoided:                    21
% 2.60/1.01  
% 2.60/1.01  ------ Simplifications
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  sim_fw_subset_subsumed:                 22
% 2.60/1.01  sim_bw_subset_subsumed:                 12
% 2.60/1.01  sim_fw_subsumed:                        2
% 2.60/1.01  sim_bw_subsumed:                        3
% 2.60/1.01  sim_fw_subsumption_res:                 0
% 2.60/1.01  sim_bw_subsumption_res:                 0
% 2.60/1.01  sim_tautology_del:                      2
% 2.60/1.01  sim_eq_tautology_del:                   14
% 2.60/1.01  sim_eq_res_simp:                        10
% 2.60/1.01  sim_fw_demodulated:                     26
% 2.60/1.01  sim_bw_demodulated:                     35
% 2.60/1.01  sim_light_normalised:                   15
% 2.60/1.01  sim_joinable_taut:                      0
% 2.60/1.01  sim_joinable_simp:                      0
% 2.60/1.01  sim_ac_normalised:                      0
% 2.60/1.01  sim_smt_subsumption:                    0
% 2.60/1.01  
%------------------------------------------------------------------------------
