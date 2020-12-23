%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:56 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  181 (6106 expanded)
%              Number of clauses        :  113 (1882 expanded)
%              Number of leaves         :   22 (1696 expanded)
%              Depth                    :   35
%              Number of atoms          :  459 (34364 expanded)
%              Number of equality atoms :  200 (13543 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1974,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_350,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_351,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_355,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_356,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_2002,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1974,c_351,c_356])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1980,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2760,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_1980])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_254,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_208])).

cnf(c_1972,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_4383,plain,
    ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2760,c_1972])).

cnf(c_10,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_362,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_363,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_365,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_26,c_24])).

cnf(c_381,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) != X1
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_365])).

cnf(c_382,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_382])).

cnf(c_418,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1489,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | sP0_iProver_split
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_418])).

cnf(c_1969,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_2055,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1969,c_351])).

cnf(c_2056,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2055,c_356])).

cnf(c_1488,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_418])).

cnf(c_1970,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_2032,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1970,c_356])).

cnf(c_2169,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_2032])).

cnf(c_2217,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2056,c_2169])).

cnf(c_2218,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2217])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1982,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1984,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2564,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_1984])).

cnf(c_2604,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_2564])).

cnf(c_3474,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_struct_0(sK1))) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_2604])).

cnf(c_2137,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_208])).

cnf(c_2498,plain,
    ( ~ r1_tarski(sK2,X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_2936,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2498])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1976,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2917,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_2002,c_1976])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1978,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2840,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2002,c_1978])).

cnf(c_3088,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2917,c_2840])).

cnf(c_22,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2013,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_22,c_351,c_356])).

cnf(c_3090,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3088,c_2013])).

cnf(c_3490,plain,
    ( ~ v1_relat_1(sK2)
    | k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_struct_0(sK1))) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3474])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3514,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3779,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_struct_0(sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3474,c_24,c_2137,c_2936,c_3090,c_3490,c_3514])).

cnf(c_14,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1977,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2759,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1977,c_1980])).

cnf(c_3789,plain,
    ( r1_tarski(k6_relat_1(k2_zfmisc_1(X0,k2_struct_0(sK1))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3779,c_2759])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1983,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3825,plain,
    ( k6_relat_1(k2_zfmisc_1(X0,k2_struct_0(sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3789,c_1983])).

cnf(c_4385,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4383,c_10,c_3825])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_1971,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_2233,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_1971])).

cnf(c_4492,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k2_struct_0(sK0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4385,c_2233])).

cnf(c_66,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_68,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_83,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1498,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2142,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_2143,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2142])).

cnf(c_2145,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_2277,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2281,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2277])).

cnf(c_5280,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4492,c_68,c_83,c_0,c_2145,c_2281])).

cnf(c_4485,plain,
    ( k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4385,c_3090])).

cnf(c_2507,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_1984])).

cnf(c_4491,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4385,c_2507])).

cnf(c_4532,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4485,c_4491])).

cnf(c_2514,plain,
    ( ~ v1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2507])).

cnf(c_4862,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4532,c_24,c_2137,c_2514,c_2936,c_3090,c_3514])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4875,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4862,c_23])).

cnf(c_4876,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4875])).

cnf(c_5284,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5280,c_4876])).

cnf(c_5288,plain,
    ( k9_relat_1(k6_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5284,c_1972])).

cnf(c_1985,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2603,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1985,c_2564])).

cnf(c_3334,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_1977])).

cnf(c_3467,plain,
    ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3334,c_1980])).

cnf(c_3552,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3467,c_1983])).

cnf(c_5290,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5288,c_3552])).

cnf(c_5291,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5290,c_10])).

cnf(c_5050,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4876,c_4485])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5291,c_5050])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.63/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/0.99  
% 2.63/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/0.99  
% 2.63/0.99  ------  iProver source info
% 2.63/0.99  
% 2.63/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.63/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/0.99  git: non_committed_changes: false
% 2.63/0.99  git: last_make_outside_of_git: false
% 2.63/0.99  
% 2.63/0.99  ------ 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options
% 2.63/0.99  
% 2.63/0.99  --out_options                           all
% 2.63/0.99  --tptp_safe_out                         true
% 2.63/0.99  --problem_path                          ""
% 2.63/0.99  --include_path                          ""
% 2.63/0.99  --clausifier                            res/vclausify_rel
% 2.63/0.99  --clausifier_options                    --mode clausify
% 2.63/0.99  --stdin                                 false
% 2.63/0.99  --stats_out                             all
% 2.63/0.99  
% 2.63/0.99  ------ General Options
% 2.63/0.99  
% 2.63/0.99  --fof                                   false
% 2.63/0.99  --time_out_real                         305.
% 2.63/0.99  --time_out_virtual                      -1.
% 2.63/0.99  --symbol_type_check                     false
% 2.63/0.99  --clausify_out                          false
% 2.63/0.99  --sig_cnt_out                           false
% 2.63/0.99  --trig_cnt_out                          false
% 2.63/0.99  --trig_cnt_out_tolerance                1.
% 2.63/0.99  --trig_cnt_out_sk_spl                   false
% 2.63/0.99  --abstr_cl_out                          false
% 2.63/0.99  
% 2.63/0.99  ------ Global Options
% 2.63/0.99  
% 2.63/0.99  --schedule                              default
% 2.63/0.99  --add_important_lit                     false
% 2.63/0.99  --prop_solver_per_cl                    1000
% 2.63/0.99  --min_unsat_core                        false
% 2.63/0.99  --soft_assumptions                      false
% 2.63/0.99  --soft_lemma_size                       3
% 2.63/0.99  --prop_impl_unit_size                   0
% 2.63/0.99  --prop_impl_unit                        []
% 2.63/0.99  --share_sel_clauses                     true
% 2.63/0.99  --reset_solvers                         false
% 2.63/0.99  --bc_imp_inh                            [conj_cone]
% 2.63/0.99  --conj_cone_tolerance                   3.
% 2.63/0.99  --extra_neg_conj                        none
% 2.63/0.99  --large_theory_mode                     true
% 2.63/0.99  --prolific_symb_bound                   200
% 2.63/0.99  --lt_threshold                          2000
% 2.63/0.99  --clause_weak_htbl                      true
% 2.63/0.99  --gc_record_bc_elim                     false
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing Options
% 2.63/0.99  
% 2.63/0.99  --preprocessing_flag                    true
% 2.63/0.99  --time_out_prep_mult                    0.1
% 2.63/0.99  --splitting_mode                        input
% 2.63/0.99  --splitting_grd                         true
% 2.63/0.99  --splitting_cvd                         false
% 2.63/0.99  --splitting_cvd_svl                     false
% 2.63/0.99  --splitting_nvd                         32
% 2.63/0.99  --sub_typing                            true
% 2.63/0.99  --prep_gs_sim                           true
% 2.63/0.99  --prep_unflatten                        true
% 2.63/0.99  --prep_res_sim                          true
% 2.63/0.99  --prep_upred                            true
% 2.63/0.99  --prep_sem_filter                       exhaustive
% 2.63/0.99  --prep_sem_filter_out                   false
% 2.63/0.99  --pred_elim                             true
% 2.63/0.99  --res_sim_input                         true
% 2.63/0.99  --eq_ax_congr_red                       true
% 2.63/0.99  --pure_diseq_elim                       true
% 2.63/0.99  --brand_transform                       false
% 2.63/0.99  --non_eq_to_eq                          false
% 2.63/0.99  --prep_def_merge                        true
% 2.63/0.99  --prep_def_merge_prop_impl              false
% 2.63/0.99  --prep_def_merge_mbd                    true
% 2.63/0.99  --prep_def_merge_tr_red                 false
% 2.63/0.99  --prep_def_merge_tr_cl                  false
% 2.63/0.99  --smt_preprocessing                     true
% 2.63/0.99  --smt_ac_axioms                         fast
% 2.63/0.99  --preprocessed_out                      false
% 2.63/0.99  --preprocessed_stats                    false
% 2.63/0.99  
% 2.63/0.99  ------ Abstraction refinement Options
% 2.63/0.99  
% 2.63/0.99  --abstr_ref                             []
% 2.63/0.99  --abstr_ref_prep                        false
% 2.63/0.99  --abstr_ref_until_sat                   false
% 2.63/0.99  --abstr_ref_sig_restrict                funpre
% 2.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.99  --abstr_ref_under                       []
% 2.63/0.99  
% 2.63/0.99  ------ SAT Options
% 2.63/0.99  
% 2.63/0.99  --sat_mode                              false
% 2.63/0.99  --sat_fm_restart_options                ""
% 2.63/0.99  --sat_gr_def                            false
% 2.63/0.99  --sat_epr_types                         true
% 2.63/0.99  --sat_non_cyclic_types                  false
% 2.63/0.99  --sat_finite_models                     false
% 2.63/0.99  --sat_fm_lemmas                         false
% 2.63/0.99  --sat_fm_prep                           false
% 2.63/0.99  --sat_fm_uc_incr                        true
% 2.63/0.99  --sat_out_model                         small
% 2.63/0.99  --sat_out_clauses                       false
% 2.63/0.99  
% 2.63/0.99  ------ QBF Options
% 2.63/0.99  
% 2.63/0.99  --qbf_mode                              false
% 2.63/0.99  --qbf_elim_univ                         false
% 2.63/0.99  --qbf_dom_inst                          none
% 2.63/0.99  --qbf_dom_pre_inst                      false
% 2.63/0.99  --qbf_sk_in                             false
% 2.63/0.99  --qbf_pred_elim                         true
% 2.63/0.99  --qbf_split                             512
% 2.63/0.99  
% 2.63/0.99  ------ BMC1 Options
% 2.63/0.99  
% 2.63/0.99  --bmc1_incremental                      false
% 2.63/0.99  --bmc1_axioms                           reachable_all
% 2.63/0.99  --bmc1_min_bound                        0
% 2.63/0.99  --bmc1_max_bound                        -1
% 2.63/0.99  --bmc1_max_bound_default                -1
% 2.63/0.99  --bmc1_symbol_reachability              true
% 2.63/0.99  --bmc1_property_lemmas                  false
% 2.63/0.99  --bmc1_k_induction                      false
% 2.63/0.99  --bmc1_non_equiv_states                 false
% 2.63/0.99  --bmc1_deadlock                         false
% 2.63/0.99  --bmc1_ucm                              false
% 2.63/0.99  --bmc1_add_unsat_core                   none
% 2.63/0.99  --bmc1_unsat_core_children              false
% 2.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.99  --bmc1_out_stat                         full
% 2.63/0.99  --bmc1_ground_init                      false
% 2.63/0.99  --bmc1_pre_inst_next_state              false
% 2.63/0.99  --bmc1_pre_inst_state                   false
% 2.63/0.99  --bmc1_pre_inst_reach_state             false
% 2.63/0.99  --bmc1_out_unsat_core                   false
% 2.63/0.99  --bmc1_aig_witness_out                  false
% 2.63/0.99  --bmc1_verbose                          false
% 2.63/0.99  --bmc1_dump_clauses_tptp                false
% 2.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.99  --bmc1_dump_file                        -
% 2.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.99  --bmc1_ucm_extend_mode                  1
% 2.63/0.99  --bmc1_ucm_init_mode                    2
% 2.63/0.99  --bmc1_ucm_cone_mode                    none
% 2.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.99  --bmc1_ucm_relax_model                  4
% 2.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.99  --bmc1_ucm_layered_model                none
% 2.63/0.99  --bmc1_ucm_max_lemma_size               10
% 2.63/0.99  
% 2.63/0.99  ------ AIG Options
% 2.63/0.99  
% 2.63/0.99  --aig_mode                              false
% 2.63/0.99  
% 2.63/0.99  ------ Instantiation Options
% 2.63/0.99  
% 2.63/0.99  --instantiation_flag                    true
% 2.63/0.99  --inst_sos_flag                         false
% 2.63/0.99  --inst_sos_phase                        true
% 2.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel_side                     num_symb
% 2.63/0.99  --inst_solver_per_active                1400
% 2.63/0.99  --inst_solver_calls_frac                1.
% 2.63/0.99  --inst_passive_queue_type               priority_queues
% 2.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.99  --inst_passive_queues_freq              [25;2]
% 2.63/0.99  --inst_dismatching                      true
% 2.63/0.99  --inst_eager_unprocessed_to_passive     true
% 2.63/0.99  --inst_prop_sim_given                   true
% 2.63/0.99  --inst_prop_sim_new                     false
% 2.63/0.99  --inst_subs_new                         false
% 2.63/0.99  --inst_eq_res_simp                      false
% 2.63/0.99  --inst_subs_given                       false
% 2.63/0.99  --inst_orphan_elimination               true
% 2.63/0.99  --inst_learning_loop_flag               true
% 2.63/0.99  --inst_learning_start                   3000
% 2.63/0.99  --inst_learning_factor                  2
% 2.63/0.99  --inst_start_prop_sim_after_learn       3
% 2.63/0.99  --inst_sel_renew                        solver
% 2.63/0.99  --inst_lit_activity_flag                true
% 2.63/0.99  --inst_restr_to_given                   false
% 2.63/0.99  --inst_activity_threshold               500
% 2.63/0.99  --inst_out_proof                        true
% 2.63/0.99  
% 2.63/0.99  ------ Resolution Options
% 2.63/0.99  
% 2.63/0.99  --resolution_flag                       true
% 2.63/0.99  --res_lit_sel                           adaptive
% 2.63/0.99  --res_lit_sel_side                      none
% 2.63/0.99  --res_ordering                          kbo
% 2.63/0.99  --res_to_prop_solver                    active
% 2.63/0.99  --res_prop_simpl_new                    false
% 2.63/0.99  --res_prop_simpl_given                  true
% 2.63/0.99  --res_passive_queue_type                priority_queues
% 2.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.99  --res_passive_queues_freq               [15;5]
% 2.63/0.99  --res_forward_subs                      full
% 2.63/0.99  --res_backward_subs                     full
% 2.63/0.99  --res_forward_subs_resolution           true
% 2.63/0.99  --res_backward_subs_resolution          true
% 2.63/0.99  --res_orphan_elimination                true
% 2.63/0.99  --res_time_limit                        2.
% 2.63/0.99  --res_out_proof                         true
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Options
% 2.63/0.99  
% 2.63/0.99  --superposition_flag                    true
% 2.63/0.99  --sup_passive_queue_type                priority_queues
% 2.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.99  --demod_completeness_check              fast
% 2.63/0.99  --demod_use_ground                      true
% 2.63/0.99  --sup_to_prop_solver                    passive
% 2.63/0.99  --sup_prop_simpl_new                    true
% 2.63/0.99  --sup_prop_simpl_given                  true
% 2.63/0.99  --sup_fun_splitting                     false
% 2.63/0.99  --sup_smt_interval                      50000
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Simplification Setup
% 2.63/0.99  
% 2.63/0.99  --sup_indices_passive                   []
% 2.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_full_bw                           [BwDemod]
% 2.63/0.99  --sup_immed_triv                        [TrivRules]
% 2.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_immed_bw_main                     []
% 2.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  
% 2.63/0.99  ------ Combination Options
% 2.63/0.99  
% 2.63/0.99  --comb_res_mult                         3
% 2.63/0.99  --comb_sup_mult                         2
% 2.63/0.99  --comb_inst_mult                        10
% 2.63/0.99  
% 2.63/0.99  ------ Debug Options
% 2.63/0.99  
% 2.63/0.99  --dbg_backtrace                         false
% 2.63/0.99  --dbg_dump_prop_clauses                 false
% 2.63/0.99  --dbg_dump_prop_clauses_file            -
% 2.63/0.99  --dbg_out_stat                          false
% 2.63/0.99  ------ Parsing...
% 2.63/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/0.99  ------ Proving...
% 2.63/0.99  ------ Problem Properties 
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  clauses                                 23
% 2.63/0.99  conjectures                             3
% 2.63/0.99  EPR                                     4
% 2.63/0.99  Horn                                    21
% 2.63/0.99  unary                                   8
% 2.63/0.99  binary                                  11
% 2.63/0.99  lits                                    44
% 2.63/0.99  lits eq                                 14
% 2.63/0.99  fd_pure                                 0
% 2.63/0.99  fd_pseudo                               0
% 2.63/0.99  fd_cond                                 2
% 2.63/0.99  fd_pseudo_cond                          0
% 2.63/0.99  AC symbols                              0
% 2.63/0.99  
% 2.63/0.99  ------ Schedule dynamic 5 is on 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  ------ 
% 2.63/0.99  Current options:
% 2.63/0.99  ------ 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options
% 2.63/0.99  
% 2.63/0.99  --out_options                           all
% 2.63/0.99  --tptp_safe_out                         true
% 2.63/0.99  --problem_path                          ""
% 2.63/0.99  --include_path                          ""
% 2.63/0.99  --clausifier                            res/vclausify_rel
% 2.63/0.99  --clausifier_options                    --mode clausify
% 2.63/0.99  --stdin                                 false
% 2.63/0.99  --stats_out                             all
% 2.63/0.99  
% 2.63/0.99  ------ General Options
% 2.63/0.99  
% 2.63/0.99  --fof                                   false
% 2.63/0.99  --time_out_real                         305.
% 2.63/0.99  --time_out_virtual                      -1.
% 2.63/0.99  --symbol_type_check                     false
% 2.63/0.99  --clausify_out                          false
% 2.63/0.99  --sig_cnt_out                           false
% 2.63/0.99  --trig_cnt_out                          false
% 2.63/0.99  --trig_cnt_out_tolerance                1.
% 2.63/0.99  --trig_cnt_out_sk_spl                   false
% 2.63/0.99  --abstr_cl_out                          false
% 2.63/0.99  
% 2.63/0.99  ------ Global Options
% 2.63/0.99  
% 2.63/0.99  --schedule                              default
% 2.63/0.99  --add_important_lit                     false
% 2.63/0.99  --prop_solver_per_cl                    1000
% 2.63/0.99  --min_unsat_core                        false
% 2.63/0.99  --soft_assumptions                      false
% 2.63/0.99  --soft_lemma_size                       3
% 2.63/0.99  --prop_impl_unit_size                   0
% 2.63/0.99  --prop_impl_unit                        []
% 2.63/0.99  --share_sel_clauses                     true
% 2.63/0.99  --reset_solvers                         false
% 2.63/0.99  --bc_imp_inh                            [conj_cone]
% 2.63/0.99  --conj_cone_tolerance                   3.
% 2.63/0.99  --extra_neg_conj                        none
% 2.63/0.99  --large_theory_mode                     true
% 2.63/0.99  --prolific_symb_bound                   200
% 2.63/0.99  --lt_threshold                          2000
% 2.63/0.99  --clause_weak_htbl                      true
% 2.63/0.99  --gc_record_bc_elim                     false
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing Options
% 2.63/0.99  
% 2.63/0.99  --preprocessing_flag                    true
% 2.63/0.99  --time_out_prep_mult                    0.1
% 2.63/0.99  --splitting_mode                        input
% 2.63/0.99  --splitting_grd                         true
% 2.63/0.99  --splitting_cvd                         false
% 2.63/0.99  --splitting_cvd_svl                     false
% 2.63/0.99  --splitting_nvd                         32
% 2.63/0.99  --sub_typing                            true
% 2.63/0.99  --prep_gs_sim                           true
% 2.63/0.99  --prep_unflatten                        true
% 2.63/0.99  --prep_res_sim                          true
% 2.63/0.99  --prep_upred                            true
% 2.63/0.99  --prep_sem_filter                       exhaustive
% 2.63/0.99  --prep_sem_filter_out                   false
% 2.63/0.99  --pred_elim                             true
% 2.63/0.99  --res_sim_input                         true
% 2.63/0.99  --eq_ax_congr_red                       true
% 2.63/0.99  --pure_diseq_elim                       true
% 2.63/0.99  --brand_transform                       false
% 2.63/0.99  --non_eq_to_eq                          false
% 2.63/0.99  --prep_def_merge                        true
% 2.63/0.99  --prep_def_merge_prop_impl              false
% 2.63/0.99  --prep_def_merge_mbd                    true
% 2.63/0.99  --prep_def_merge_tr_red                 false
% 2.63/0.99  --prep_def_merge_tr_cl                  false
% 2.63/0.99  --smt_preprocessing                     true
% 2.63/0.99  --smt_ac_axioms                         fast
% 2.63/0.99  --preprocessed_out                      false
% 2.63/0.99  --preprocessed_stats                    false
% 2.63/0.99  
% 2.63/0.99  ------ Abstraction refinement Options
% 2.63/0.99  
% 2.63/0.99  --abstr_ref                             []
% 2.63/0.99  --abstr_ref_prep                        false
% 2.63/0.99  --abstr_ref_until_sat                   false
% 2.63/0.99  --abstr_ref_sig_restrict                funpre
% 2.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.99  --abstr_ref_under                       []
% 2.63/0.99  
% 2.63/0.99  ------ SAT Options
% 2.63/0.99  
% 2.63/0.99  --sat_mode                              false
% 2.63/0.99  --sat_fm_restart_options                ""
% 2.63/0.99  --sat_gr_def                            false
% 2.63/0.99  --sat_epr_types                         true
% 2.63/0.99  --sat_non_cyclic_types                  false
% 2.63/0.99  --sat_finite_models                     false
% 2.63/0.99  --sat_fm_lemmas                         false
% 2.63/0.99  --sat_fm_prep                           false
% 2.63/0.99  --sat_fm_uc_incr                        true
% 2.63/0.99  --sat_out_model                         small
% 2.63/0.99  --sat_out_clauses                       false
% 2.63/0.99  
% 2.63/0.99  ------ QBF Options
% 2.63/0.99  
% 2.63/0.99  --qbf_mode                              false
% 2.63/0.99  --qbf_elim_univ                         false
% 2.63/0.99  --qbf_dom_inst                          none
% 2.63/0.99  --qbf_dom_pre_inst                      false
% 2.63/0.99  --qbf_sk_in                             false
% 2.63/0.99  --qbf_pred_elim                         true
% 2.63/0.99  --qbf_split                             512
% 2.63/0.99  
% 2.63/0.99  ------ BMC1 Options
% 2.63/0.99  
% 2.63/0.99  --bmc1_incremental                      false
% 2.63/0.99  --bmc1_axioms                           reachable_all
% 2.63/0.99  --bmc1_min_bound                        0
% 2.63/0.99  --bmc1_max_bound                        -1
% 2.63/0.99  --bmc1_max_bound_default                -1
% 2.63/0.99  --bmc1_symbol_reachability              true
% 2.63/0.99  --bmc1_property_lemmas                  false
% 2.63/0.99  --bmc1_k_induction                      false
% 2.63/0.99  --bmc1_non_equiv_states                 false
% 2.63/0.99  --bmc1_deadlock                         false
% 2.63/0.99  --bmc1_ucm                              false
% 2.63/0.99  --bmc1_add_unsat_core                   none
% 2.63/0.99  --bmc1_unsat_core_children              false
% 2.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.99  --bmc1_out_stat                         full
% 2.63/0.99  --bmc1_ground_init                      false
% 2.63/0.99  --bmc1_pre_inst_next_state              false
% 2.63/0.99  --bmc1_pre_inst_state                   false
% 2.63/0.99  --bmc1_pre_inst_reach_state             false
% 2.63/0.99  --bmc1_out_unsat_core                   false
% 2.63/0.99  --bmc1_aig_witness_out                  false
% 2.63/0.99  --bmc1_verbose                          false
% 2.63/0.99  --bmc1_dump_clauses_tptp                false
% 2.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.99  --bmc1_dump_file                        -
% 2.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.99  --bmc1_ucm_extend_mode                  1
% 2.63/0.99  --bmc1_ucm_init_mode                    2
% 2.63/0.99  --bmc1_ucm_cone_mode                    none
% 2.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.99  --bmc1_ucm_relax_model                  4
% 2.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.99  --bmc1_ucm_layered_model                none
% 2.63/0.99  --bmc1_ucm_max_lemma_size               10
% 2.63/0.99  
% 2.63/0.99  ------ AIG Options
% 2.63/0.99  
% 2.63/0.99  --aig_mode                              false
% 2.63/0.99  
% 2.63/0.99  ------ Instantiation Options
% 2.63/0.99  
% 2.63/0.99  --instantiation_flag                    true
% 2.63/0.99  --inst_sos_flag                         false
% 2.63/0.99  --inst_sos_phase                        true
% 2.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel_side                     none
% 2.63/0.99  --inst_solver_per_active                1400
% 2.63/0.99  --inst_solver_calls_frac                1.
% 2.63/0.99  --inst_passive_queue_type               priority_queues
% 2.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.99  --inst_passive_queues_freq              [25;2]
% 2.63/0.99  --inst_dismatching                      true
% 2.63/0.99  --inst_eager_unprocessed_to_passive     true
% 2.63/0.99  --inst_prop_sim_given                   true
% 2.63/0.99  --inst_prop_sim_new                     false
% 2.63/0.99  --inst_subs_new                         false
% 2.63/0.99  --inst_eq_res_simp                      false
% 2.63/0.99  --inst_subs_given                       false
% 2.63/0.99  --inst_orphan_elimination               true
% 2.63/0.99  --inst_learning_loop_flag               true
% 2.63/0.99  --inst_learning_start                   3000
% 2.63/0.99  --inst_learning_factor                  2
% 2.63/0.99  --inst_start_prop_sim_after_learn       3
% 2.63/0.99  --inst_sel_renew                        solver
% 2.63/0.99  --inst_lit_activity_flag                true
% 2.63/0.99  --inst_restr_to_given                   false
% 2.63/0.99  --inst_activity_threshold               500
% 2.63/0.99  --inst_out_proof                        true
% 2.63/0.99  
% 2.63/0.99  ------ Resolution Options
% 2.63/0.99  
% 2.63/0.99  --resolution_flag                       false
% 2.63/0.99  --res_lit_sel                           adaptive
% 2.63/0.99  --res_lit_sel_side                      none
% 2.63/0.99  --res_ordering                          kbo
% 2.63/0.99  --res_to_prop_solver                    active
% 2.63/0.99  --res_prop_simpl_new                    false
% 2.63/0.99  --res_prop_simpl_given                  true
% 2.63/0.99  --res_passive_queue_type                priority_queues
% 2.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.99  --res_passive_queues_freq               [15;5]
% 2.63/0.99  --res_forward_subs                      full
% 2.63/0.99  --res_backward_subs                     full
% 2.63/0.99  --res_forward_subs_resolution           true
% 2.63/0.99  --res_backward_subs_resolution          true
% 2.63/0.99  --res_orphan_elimination                true
% 2.63/0.99  --res_time_limit                        2.
% 2.63/0.99  --res_out_proof                         true
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Options
% 2.63/0.99  
% 2.63/0.99  --superposition_flag                    true
% 2.63/0.99  --sup_passive_queue_type                priority_queues
% 2.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.99  --demod_completeness_check              fast
% 2.63/0.99  --demod_use_ground                      true
% 2.63/0.99  --sup_to_prop_solver                    passive
% 2.63/0.99  --sup_prop_simpl_new                    true
% 2.63/0.99  --sup_prop_simpl_given                  true
% 2.63/0.99  --sup_fun_splitting                     false
% 2.63/0.99  --sup_smt_interval                      50000
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Simplification Setup
% 2.63/0.99  
% 2.63/0.99  --sup_indices_passive                   []
% 2.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_full_bw                           [BwDemod]
% 2.63/0.99  --sup_immed_triv                        [TrivRules]
% 2.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_immed_bw_main                     []
% 2.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  
% 2.63/0.99  ------ Combination Options
% 2.63/0.99  
% 2.63/0.99  --comb_res_mult                         3
% 2.63/0.99  --comb_sup_mult                         2
% 2.63/0.99  --comb_inst_mult                        10
% 2.63/0.99  
% 2.63/0.99  ------ Debug Options
% 2.63/0.99  
% 2.63/0.99  --dbg_backtrace                         false
% 2.63/0.99  --dbg_dump_prop_clauses                 false
% 2.63/0.99  --dbg_dump_prop_clauses_file            -
% 2.63/0.99  --dbg_out_stat                          false
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  ------ Proving...
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  % SZS status Theorem for theBenchmark.p
% 2.63/0.99  
% 2.63/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/0.99  
% 2.63/0.99  fof(f18,conjecture,(
% 2.63/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f19,negated_conjecture,(
% 2.63/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.63/0.99    inference(negated_conjecture,[],[f18])).
% 2.63/0.99  
% 2.63/0.99  fof(f35,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f19])).
% 2.63/0.99  
% 2.63/0.99  fof(f36,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.63/0.99    inference(flattening,[],[f35])).
% 2.63/0.99  
% 2.63/0.99  fof(f42,plain,(
% 2.63/0.99    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f41,plain,(
% 2.63/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f40,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f43,plain,(
% 2.63/0.99    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).
% 2.63/0.99  
% 2.63/0.99  fof(f70,plain,(
% 2.63/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.63/0.99    inference(cnf_transformation,[],[f43])).
% 2.63/0.99  
% 2.63/0.99  fof(f17,axiom,(
% 2.63/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f34,plain,(
% 2.63/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f17])).
% 2.63/0.99  
% 2.63/0.99  fof(f65,plain,(
% 2.63/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f34])).
% 2.63/0.99  
% 2.63/0.99  fof(f67,plain,(
% 2.63/0.99    l1_struct_0(sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f43])).
% 2.63/0.99  
% 2.63/0.99  fof(f66,plain,(
% 2.63/0.99    l1_struct_0(sK0)),
% 2.63/0.99    inference(cnf_transformation,[],[f43])).
% 2.63/0.99  
% 2.63/0.99  fof(f5,axiom,(
% 2.63/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f37,plain,(
% 2.63/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.63/0.99    inference(nnf_transformation,[],[f5])).
% 2.63/0.99  
% 2.63/0.99  fof(f48,plain,(
% 2.63/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f37])).
% 2.63/0.99  
% 2.63/0.99  fof(f10,axiom,(
% 2.63/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f26,plain,(
% 2.63/0.99    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.63/0.99    inference(ennf_transformation,[],[f10])).
% 2.63/0.99  
% 2.63/0.99  fof(f55,plain,(
% 2.63/0.99    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f26])).
% 2.63/0.99  
% 2.63/0.99  fof(f49,plain,(
% 2.63/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f37])).
% 2.63/0.99  
% 2.63/0.99  fof(f9,axiom,(
% 2.63/0.99    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f54,plain,(
% 2.63/0.99    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f9])).
% 2.63/0.99  
% 2.63/0.99  fof(f11,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f20,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.63/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.63/0.99  
% 2.63/0.99  fof(f27,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/0.99    inference(ennf_transformation,[],[f20])).
% 2.63/0.99  
% 2.63/0.99  fof(f56,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f27])).
% 2.63/0.99  
% 2.63/0.99  fof(f16,axiom,(
% 2.63/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f32,plain,(
% 2.63/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.63/0.99    inference(ennf_transformation,[],[f16])).
% 2.63/0.99  
% 2.63/0.99  fof(f33,plain,(
% 2.63/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.63/0.99    inference(flattening,[],[f32])).
% 2.63/0.99  
% 2.63/0.99  fof(f39,plain,(
% 2.63/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.63/0.99    inference(nnf_transformation,[],[f33])).
% 2.63/0.99  
% 2.63/0.99  fof(f63,plain,(
% 2.63/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f39])).
% 2.63/0.99  
% 2.63/0.99  fof(f15,axiom,(
% 2.63/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f30,plain,(
% 2.63/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.63/0.99    inference(ennf_transformation,[],[f15])).
% 2.63/0.99  
% 2.63/0.99  fof(f31,plain,(
% 2.63/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.63/0.99    inference(flattening,[],[f30])).
% 2.63/0.99  
% 2.63/0.99  fof(f62,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f31])).
% 2.63/0.99  
% 2.63/0.99  fof(f69,plain,(
% 2.63/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.63/0.99    inference(cnf_transformation,[],[f43])).
% 2.63/0.99  
% 2.63/0.99  fof(f68,plain,(
% 2.63/0.99    v1_funct_1(sK2)),
% 2.63/0.99    inference(cnf_transformation,[],[f43])).
% 2.63/0.99  
% 2.63/0.99  fof(f4,axiom,(
% 2.63/0.99    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f23,plain,(
% 2.63/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 2.63/0.99    inference(ennf_transformation,[],[f4])).
% 2.63/0.99  
% 2.63/0.99  fof(f47,plain,(
% 2.63/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f23])).
% 2.63/0.99  
% 2.63/0.99  fof(f2,axiom,(
% 2.63/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f21,plain,(
% 2.63/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f2])).
% 2.63/0.99  
% 2.63/0.99  fof(f45,plain,(
% 2.63/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f21])).
% 2.63/0.99  
% 2.63/0.99  fof(f6,axiom,(
% 2.63/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f24,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f6])).
% 2.63/0.99  
% 2.63/0.99  fof(f50,plain,(
% 2.63/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f24])).
% 2.63/0.99  
% 2.63/0.99  fof(f14,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f29,plain,(
% 2.63/0.99    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/0.99    inference(ennf_transformation,[],[f14])).
% 2.63/0.99  
% 2.63/0.99  fof(f60,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f29])).
% 2.63/0.99  
% 2.63/0.99  fof(f12,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f28,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/0.99    inference(ennf_transformation,[],[f12])).
% 2.63/0.99  
% 2.63/0.99  fof(f57,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f28])).
% 2.63/0.99  
% 2.63/0.99  fof(f72,plain,(
% 2.63/0.99    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 2.63/0.99    inference(cnf_transformation,[],[f43])).
% 2.63/0.99  
% 2.63/0.99  fof(f8,axiom,(
% 2.63/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f53,plain,(
% 2.63/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f8])).
% 2.63/0.99  
% 2.63/0.99  fof(f13,axiom,(
% 2.63/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f58,plain,(
% 2.63/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f13])).
% 2.63/0.99  
% 2.63/0.99  fof(f3,axiom,(
% 2.63/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f22,plain,(
% 2.63/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.63/0.99    inference(ennf_transformation,[],[f3])).
% 2.63/0.99  
% 2.63/0.99  fof(f46,plain,(
% 2.63/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f22])).
% 2.63/0.99  
% 2.63/0.99  fof(f7,axiom,(
% 2.63/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f25,plain,(
% 2.63/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.63/0.99    inference(ennf_transformation,[],[f7])).
% 2.63/0.99  
% 2.63/0.99  fof(f38,plain,(
% 2.63/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.63/0.99    inference(nnf_transformation,[],[f25])).
% 2.63/0.99  
% 2.63/0.99  fof(f51,plain,(
% 2.63/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f38])).
% 2.63/0.99  
% 2.63/0.99  fof(f1,axiom,(
% 2.63/0.99    v1_xboole_0(k1_xboole_0)),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f44,plain,(
% 2.63/0.99    v1_xboole_0(k1_xboole_0)),
% 2.63/0.99    inference(cnf_transformation,[],[f1])).
% 2.63/0.99  
% 2.63/0.99  fof(f71,plain,(
% 2.63/0.99    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f43])).
% 2.63/0.99  
% 2.63/0.99  cnf(c_24,negated_conjecture,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.63/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1974,plain,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_21,plain,
% 2.63/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_27,negated_conjecture,
% 2.63/0.99      ( l1_struct_0(sK1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_350,plain,
% 2.63/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_351,plain,
% 2.63/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_350]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_28,negated_conjecture,
% 2.63/0.99      ( l1_struct_0(sK0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_355,plain,
% 2.63/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_356,plain,
% 2.63/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_355]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2002,plain,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1974,c_351,c_356]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1980,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.63/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2760,plain,
% 2.63/0.99      ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2002,c_1980]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_11,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.63/0.99      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_207,plain,
% 2.63/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.63/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_208,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.63/0.99      inference(renaming,[status(thm)],[c_207]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_254,plain,
% 2.63/0.99      ( ~ r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 2.63/0.99      inference(bin_hyper_res,[status(thm)],[c_11,c_208]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1972,plain,
% 2.63/0.99      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 2.63/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4383,plain,
% 2.63/0.99      ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) = sK2 ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2760,c_1972]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_10,plain,
% 2.63/0.99      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_12,plain,
% 2.63/0.99      ( v4_relat_1(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.63/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_20,plain,
% 2.63/0.99      ( ~ v1_partfun1(X0,X1)
% 2.63/0.99      | ~ v4_relat_1(X0,X1)
% 2.63/0.99      | ~ v1_relat_1(X0)
% 2.63/0.99      | k1_relat_1(X0) = X1 ),
% 2.63/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_17,plain,
% 2.63/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/0.99      | v1_partfun1(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/0.99      | ~ v1_funct_1(X0)
% 2.63/0.99      | v1_xboole_0(X2) ),
% 2.63/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_25,negated_conjecture,
% 2.63/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.63/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_362,plain,
% 2.63/0.99      ( v1_partfun1(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/0.99      | ~ v1_funct_1(X0)
% 2.63/0.99      | v1_xboole_0(X2)
% 2.63/0.99      | u1_struct_0(sK1) != X2
% 2.63/0.99      | u1_struct_0(sK0) != X1
% 2.63/0.99      | sK2 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_363,plain,
% 2.63/0.99      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.63/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/0.99      | ~ v1_funct_1(sK2)
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_26,negated_conjecture,
% 2.63/0.99      ( v1_funct_1(sK2) ),
% 2.63/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_365,plain,
% 2.63/0.99      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_363,c_26,c_24]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_381,plain,
% 2.63/0.99      ( ~ v4_relat_1(X0,X1)
% 2.63/0.99      | ~ v1_relat_1(X0)
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 2.63/0.99      | u1_struct_0(sK0) != X1
% 2.63/0.99      | k1_relat_1(X0) = X1
% 2.63/0.99      | sK2 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_365]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_382,plain,
% 2.63/0.99      ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
% 2.63/0.99      | ~ v1_relat_1(sK2)
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 2.63/0.99      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_381]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_417,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/0.99      | ~ v1_relat_1(sK2)
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 2.63/0.99      | u1_struct_0(sK0) != X1
% 2.63/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/0.99      | sK2 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_382]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_418,plain,
% 2.63/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.63/0.99      | ~ v1_relat_1(sK2)
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 2.63/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_417]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1489,plain,
% 2.63/0.99      ( ~ v1_relat_1(sK2)
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 2.63/0.99      | sP0_iProver_split
% 2.63/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.63/0.99      inference(splitting,
% 2.63/0.99                [splitting(split),new_symbols(definition,[])],
% 2.63/0.99                [c_418]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1969,plain,
% 2.63/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top
% 2.63/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 2.63/0.99      | sP0_iProver_split = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1489]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2055,plain,
% 2.63/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top
% 2.63/0.99      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 2.63/0.99      | sP0_iProver_split = iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1969,c_351]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2056,plain,
% 2.63/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top
% 2.63/0.99      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 2.63/0.99      | sP0_iProver_split = iProver_top ),
% 2.63/0.99      inference(demodulation,[status(thm)],[c_2055,c_356]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1488,plain,
% 2.63/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.63/0.99      | ~ sP0_iProver_split ),
% 2.63/0.99      inference(splitting,
% 2.63/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.63/0.99                [c_418]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1970,plain,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) != iProver_top
% 2.63/0.99      | sP0_iProver_split != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2032,plain,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 2.63/0.99      | sP0_iProver_split != iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1970,c_356]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2169,plain,
% 2.63/0.99      ( sP0_iProver_split != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2002,c_2032]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2217,plain,
% 2.63/0.99      ( v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top
% 2.63/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_2056,c_2169]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2218,plain,
% 2.63/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top
% 2.63/0.99      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.63/0.99      inference(renaming,[status(thm)],[c_2217]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3,plain,
% 2.63/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 2.63/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1982,plain,
% 2.63/0.99      ( v1_xboole_0(X0) != iProver_top
% 2.63/0.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1,plain,
% 2.63/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1984,plain,
% 2.63/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2564,plain,
% 2.63/0.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 2.63/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1982,c_1984]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2604,plain,
% 2.63/0.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)) = k1_xboole_0
% 2.63/0.99      | v1_xboole_0(X2) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1982,c_2564]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3474,plain,
% 2.63/0.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_struct_0(sK1))) = k1_xboole_0
% 2.63/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2218,c_2604]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2137,plain,
% 2.63/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/0.99      | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_6,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.63/0.99      | ~ v1_relat_1(X1)
% 2.63/0.99      | v1_relat_1(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_253,plain,
% 2.63/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.63/0.99      inference(bin_hyper_res,[status(thm)],[c_6,c_208]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2498,plain,
% 2.63/0.99      ( ~ r1_tarski(sK2,X0) | ~ v1_relat_1(X0) | v1_relat_1(sK2) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_253]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2936,plain,
% 2.63/0.99      ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.63/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.63/0.99      | v1_relat_1(sK2) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_2498]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_15,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/0.99      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1976,plain,
% 2.63/0.99      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.63/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2917,plain,
% 2.63/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2002,c_1976]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_13,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1978,plain,
% 2.63/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.63/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2840,plain,
% 2.63/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2002,c_1978]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3088,plain,
% 2.63/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_2917,c_2840]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_22,negated_conjecture,
% 2.63/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2013,plain,
% 2.63/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_22,c_351,c_356]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3090,plain,
% 2.63/0.99      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.63/0.99      inference(demodulation,[status(thm)],[c_3088,c_2013]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3490,plain,
% 2.63/0.99      ( ~ v1_relat_1(sK2)
% 2.63/0.99      | k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_struct_0(sK1))) = k1_xboole_0
% 2.63/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.63/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3474]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_9,plain,
% 2.63/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.63/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3514,plain,
% 2.63/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3779,plain,
% 2.63/0.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_struct_0(sK1))) = k1_xboole_0 ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_3474,c_24,c_2137,c_2936,c_3090,c_3490,c_3514]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_14,plain,
% 2.63/0.99      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.63/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1977,plain,
% 2.63/0.99      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2759,plain,
% 2.63/0.99      ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1977,c_1980]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3789,plain,
% 2.63/0.99      ( r1_tarski(k6_relat_1(k2_zfmisc_1(X0,k2_struct_0(sK1))),k1_xboole_0) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_3779,c_2759]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2,plain,
% 2.63/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1983,plain,
% 2.63/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3825,plain,
% 2.63/0.99      ( k6_relat_1(k2_zfmisc_1(X0,k2_struct_0(sK1))) = k1_xboole_0 ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_3789,c_1983]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4385,plain,
% 2.63/0.99      ( sK2 = k1_xboole_0 ),
% 2.63/0.99      inference(demodulation,[status(thm)],[c_4383,c_10,c_3825]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_8,plain,
% 2.63/0.99      ( ~ v4_relat_1(X0,X1)
% 2.63/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.63/0.99      | ~ v1_relat_1(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_402,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.63/0.99      | ~ v1_relat_1(X0) ),
% 2.63/0.99      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1971,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.63/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.63/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2233,plain,
% 2.63/0.99      ( r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2002,c_1971]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4492,plain,
% 2.63/0.99      ( r1_tarski(k1_relat_1(k1_xboole_0),k2_struct_0(sK0)) = iProver_top
% 2.63/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.63/0.99      inference(demodulation,[status(thm)],[c_4385,c_2233]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_66,plain,
% 2.63/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_68,plain,
% 2.63/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_66]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_83,plain,
% 2.63/0.99      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.63/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_0,plain,
% 2.63/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1498,plain,
% 2.63/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.63/0.99      theory(equality) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2142,plain,
% 2.63/0.99      ( v1_relat_1(X0)
% 2.63/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 2.63/0.99      | X0 != k2_zfmisc_1(X1,X2) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_1498]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2143,plain,
% 2.63/0.99      ( X0 != k2_zfmisc_1(X1,X2)
% 2.63/0.99      | v1_relat_1(X0) = iProver_top
% 2.63/0.99      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2142]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2145,plain,
% 2.63/0.99      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 2.63/0.99      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.63/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_2143]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2277,plain,
% 2.63/0.99      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
% 2.63/0.99      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2281,plain,
% 2.63/0.99      ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.63/0.99      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_2277]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5280,plain,
% 2.63/0.99      ( r1_tarski(k1_relat_1(k1_xboole_0),k2_struct_0(sK0)) = iProver_top ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_4492,c_68,c_83,c_0,c_2145,c_2281]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4485,plain,
% 2.63/0.99      ( k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
% 2.63/0.99      inference(demodulation,[status(thm)],[c_4385,c_3090]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2507,plain,
% 2.63/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.63/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2218,c_1984]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4491,plain,
% 2.63/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.63/0.99      | k2_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 2.63/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.63/0.99      inference(demodulation,[status(thm)],[c_4385,c_2507]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4532,plain,
% 2.63/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.63/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.63/0.99      inference(backward_subsumption_resolution,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_4485,c_4491]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2514,plain,
% 2.63/0.99      ( ~ v1_relat_1(sK2)
% 2.63/0.99      | k2_struct_0(sK1) = k1_xboole_0
% 2.63/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.63/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2507]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4862,plain,
% 2.63/1.00      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_4532,c_24,c_2137,c_2514,c_2936,c_3090,c_3514]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_23,negated_conjecture,
% 2.63/1.00      ( k1_xboole_0 != k2_struct_0(sK1)
% 2.63/1.00      | k1_xboole_0 = k2_struct_0(sK0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4875,plain,
% 2.63/1.00      ( k2_struct_0(sK0) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_4862,c_23]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4876,plain,
% 2.63/1.00      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 2.63/1.00      inference(equality_resolution_simp,[status(thm)],[c_4875]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5284,plain,
% 2.63/1.00      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_5280,c_4876]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5288,plain,
% 2.63/1.00      ( k9_relat_1(k6_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_5284,c_1972]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1985,plain,
% 2.63/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2603,plain,
% 2.63/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1985,c_2564]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3334,plain,
% 2.63/1.00      ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2603,c_1977]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3467,plain,
% 2.63/1.00      ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3334,c_1980]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3552,plain,
% 2.63/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3467,c_1983]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5290,plain,
% 2.63/1.00      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_5288,c_3552]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5291,plain,
% 2.63/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_5290,c_10]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5050,plain,
% 2.63/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_4876,c_4485]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(contradiction,plain,
% 2.63/1.00      ( $false ),
% 2.63/1.00      inference(minisat,[status(thm)],[c_5291,c_5050]) ).
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  ------                               Statistics
% 2.63/1.00  
% 2.63/1.00  ------ General
% 2.63/1.00  
% 2.63/1.00  abstr_ref_over_cycles:                  0
% 2.63/1.00  abstr_ref_under_cycles:                 0
% 2.63/1.00  gc_basic_clause_elim:                   0
% 2.63/1.00  forced_gc_time:                         0
% 2.63/1.00  parsing_time:                           0.01
% 2.63/1.00  unif_index_cands_time:                  0.
% 2.63/1.00  unif_index_add_time:                    0.
% 2.63/1.00  orderings_time:                         0.
% 2.63/1.00  out_proof_time:                         0.011
% 2.63/1.00  total_time:                             0.169
% 2.63/1.00  num_of_symbols:                         56
% 2.63/1.00  num_of_terms:                           3368
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing
% 2.63/1.00  
% 2.63/1.00  num_of_splits:                          1
% 2.63/1.00  num_of_split_atoms:                     1
% 2.63/1.00  num_of_reused_defs:                     0
% 2.63/1.00  num_eq_ax_congr_red:                    39
% 2.63/1.00  num_of_sem_filtered_clauses:            1
% 2.63/1.00  num_of_subtypes:                        0
% 2.63/1.00  monotx_restored_types:                  0
% 2.63/1.00  sat_num_of_epr_types:                   0
% 2.63/1.00  sat_num_of_non_cyclic_types:            0
% 2.63/1.00  sat_guarded_non_collapsed_types:        0
% 2.63/1.00  num_pure_diseq_elim:                    0
% 2.63/1.00  simp_replaced_by:                       0
% 2.63/1.00  res_preprocessed:                       123
% 2.63/1.00  prep_upred:                             0
% 2.63/1.00  prep_unflattend:                        69
% 2.63/1.00  smt_new_axioms:                         0
% 2.63/1.00  pred_elim_cands:                        4
% 2.63/1.00  pred_elim:                              5
% 2.63/1.00  pred_elim_cl:                           6
% 2.63/1.00  pred_elim_cycles:                       9
% 2.63/1.00  merged_defs:                            8
% 2.63/1.00  merged_defs_ncl:                        0
% 2.63/1.00  bin_hyper_res:                          10
% 2.63/1.00  prep_cycles:                            4
% 2.63/1.00  pred_elim_time:                         0.017
% 2.63/1.00  splitting_time:                         0.
% 2.63/1.00  sem_filter_time:                        0.
% 2.63/1.00  monotx_time:                            0.001
% 2.63/1.00  subtype_inf_time:                       0.
% 2.63/1.00  
% 2.63/1.00  ------ Problem properties
% 2.63/1.00  
% 2.63/1.00  clauses:                                23
% 2.63/1.00  conjectures:                            3
% 2.63/1.00  epr:                                    4
% 2.63/1.00  horn:                                   21
% 2.63/1.00  ground:                                 8
% 2.63/1.00  unary:                                  8
% 2.63/1.00  binary:                                 11
% 2.63/1.00  lits:                                   44
% 2.63/1.00  lits_eq:                                14
% 2.63/1.00  fd_pure:                                0
% 2.63/1.00  fd_pseudo:                              0
% 2.63/1.00  fd_cond:                                2
% 2.63/1.00  fd_pseudo_cond:                         0
% 2.63/1.00  ac_symbols:                             0
% 2.63/1.00  
% 2.63/1.00  ------ Propositional Solver
% 2.63/1.00  
% 2.63/1.00  prop_solver_calls:                      28
% 2.63/1.00  prop_fast_solver_calls:                 811
% 2.63/1.00  smt_solver_calls:                       0
% 2.63/1.00  smt_fast_solver_calls:                  0
% 2.63/1.00  prop_num_of_clauses:                    1697
% 2.63/1.00  prop_preprocess_simplified:             5048
% 2.63/1.00  prop_fo_subsumed:                       8
% 2.63/1.00  prop_solver_time:                       0.
% 2.63/1.00  smt_solver_time:                        0.
% 2.63/1.00  smt_fast_solver_time:                   0.
% 2.63/1.00  prop_fast_solver_time:                  0.
% 2.63/1.00  prop_unsat_core_time:                   0.
% 2.63/1.00  
% 2.63/1.00  ------ QBF
% 2.63/1.00  
% 2.63/1.00  qbf_q_res:                              0
% 2.63/1.00  qbf_num_tautologies:                    0
% 2.63/1.00  qbf_prep_cycles:                        0
% 2.63/1.00  
% 2.63/1.00  ------ BMC1
% 2.63/1.00  
% 2.63/1.00  bmc1_current_bound:                     -1
% 2.63/1.00  bmc1_last_solved_bound:                 -1
% 2.63/1.00  bmc1_unsat_core_size:                   -1
% 2.63/1.00  bmc1_unsat_core_parents_size:           -1
% 2.63/1.00  bmc1_merge_next_fun:                    0
% 2.63/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation
% 2.63/1.00  
% 2.63/1.00  inst_num_of_clauses:                    573
% 2.63/1.00  inst_num_in_passive:                    53
% 2.63/1.00  inst_num_in_active:                     265
% 2.63/1.00  inst_num_in_unprocessed:                255
% 2.63/1.00  inst_num_of_loops:                      310
% 2.63/1.00  inst_num_of_learning_restarts:          0
% 2.63/1.00  inst_num_moves_active_passive:          42
% 2.63/1.00  inst_lit_activity:                      0
% 2.63/1.00  inst_lit_activity_moves:                0
% 2.63/1.00  inst_num_tautologies:                   0
% 2.63/1.00  inst_num_prop_implied:                  0
% 2.63/1.00  inst_num_existing_simplified:           0
% 2.63/1.00  inst_num_eq_res_simplified:             0
% 2.63/1.00  inst_num_child_elim:                    0
% 2.63/1.00  inst_num_of_dismatching_blockings:      134
% 2.63/1.00  inst_num_of_non_proper_insts:           444
% 2.63/1.00  inst_num_of_duplicates:                 0
% 2.63/1.00  inst_inst_num_from_inst_to_res:         0
% 2.63/1.00  inst_dismatching_checking_time:         0.
% 2.63/1.00  
% 2.63/1.00  ------ Resolution
% 2.63/1.00  
% 2.63/1.00  res_num_of_clauses:                     0
% 2.63/1.00  res_num_in_passive:                     0
% 2.63/1.00  res_num_in_active:                      0
% 2.63/1.00  res_num_of_loops:                       127
% 2.63/1.00  res_forward_subset_subsumed:            50
% 2.63/1.00  res_backward_subset_subsumed:           4
% 2.63/1.00  res_forward_subsumed:                   0
% 2.63/1.00  res_backward_subsumed:                  0
% 2.63/1.00  res_forward_subsumption_resolution:     0
% 2.63/1.00  res_backward_subsumption_resolution:    0
% 2.63/1.00  res_clause_to_clause_subsumption:       147
% 2.63/1.00  res_orphan_elimination:                 0
% 2.63/1.00  res_tautology_del:                      77
% 2.63/1.00  res_num_eq_res_simplified:              0
% 2.63/1.00  res_num_sel_changes:                    0
% 2.63/1.00  res_moves_from_active_to_pass:          0
% 2.63/1.00  
% 2.63/1.00  ------ Superposition
% 2.63/1.00  
% 2.63/1.00  sup_time_total:                         0.
% 2.63/1.00  sup_time_generating:                    0.
% 2.63/1.00  sup_time_sim_full:                      0.
% 2.63/1.00  sup_time_sim_immed:                     0.
% 2.63/1.00  
% 2.63/1.00  sup_num_of_clauses:                     65
% 2.63/1.00  sup_num_in_active:                      32
% 2.63/1.00  sup_num_in_passive:                     33
% 2.63/1.00  sup_num_of_loops:                       60
% 2.63/1.00  sup_fw_superposition:                   43
% 2.63/1.00  sup_bw_superposition:                   39
% 2.63/1.00  sup_immediate_simplified:               31
% 2.63/1.00  sup_given_eliminated:                   1
% 2.63/1.00  comparisons_done:                       0
% 2.63/1.00  comparisons_avoided:                    6
% 2.63/1.00  
% 2.63/1.00  ------ Simplifications
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  sim_fw_subset_subsumed:                 4
% 2.63/1.00  sim_bw_subset_subsumed:                 0
% 2.63/1.00  sim_fw_subsumed:                        0
% 2.63/1.00  sim_bw_subsumed:                        0
% 2.63/1.00  sim_fw_subsumption_res:                 0
% 2.63/1.00  sim_bw_subsumption_res:                 3
% 2.63/1.00  sim_tautology_del:                      2
% 2.63/1.00  sim_eq_tautology_del:                   4
% 2.63/1.00  sim_eq_res_simp:                        1
% 2.63/1.00  sim_fw_demodulated:                     16
% 2.63/1.00  sim_bw_demodulated:                     30
% 2.63/1.00  sim_light_normalised:                   21
% 2.63/1.00  sim_joinable_taut:                      0
% 2.63/1.00  sim_joinable_simp:                      0
% 2.63/1.00  sim_ac_normalised:                      0
% 2.63/1.00  sim_smt_subsumption:                    0
% 2.63/1.00  
%------------------------------------------------------------------------------
