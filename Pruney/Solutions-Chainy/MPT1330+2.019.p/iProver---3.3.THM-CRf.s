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
% DateTime   : Thu Dec  3 12:16:56 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  172 (2373 expanded)
%              Number of clauses        :  109 ( 779 expanded)
%              Number of leaves         :   18 ( 638 expanded)
%              Depth                    :   27
%              Number of atoms          :  524 (13432 expanded)
%              Number of equality atoms :  209 (5294 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
          & ( k1_xboole_0 = k2_struct_0(X0)
            | k1_xboole_0 != k2_struct_0(X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0)
        & ( k1_xboole_0 = k2_struct_0(X0)
          | k1_xboole_0 != k2_struct_0(X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0)
            & ( k1_xboole_0 = k2_struct_0(X0)
              | k1_xboole_0 != k2_struct_0(sK2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
              ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1)
              & ( k1_xboole_0 = k2_struct_0(sK1)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)
    & ( k1_xboole_0 = k2_struct_0(sK1)
      | k1_xboole_0 != k2_struct_0(sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f40,f39,f38])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_753,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1034,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_314,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_315,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_751,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_309,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_310,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_752,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_310])).

cnf(c_1055,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1034,c_751,c_752])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_181,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_484,plain,
    ( ~ v4_relat_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_relat_1(X0)
    | X1 != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_181,c_6])).

cnf(c_485,plain,
    ( ~ v4_relat_1(X0,X1)
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_485])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_1035,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52)) = iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_1643,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1035])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1179,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X1_52,X2_52)) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_1217,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_759,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1249,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_1250,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_2188,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1643,c_29,c_1217,c_1250])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_338,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_339,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_341,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_22,c_20])).

cnf(c_355,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | u1_struct_0(sK2) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_341])).

cnf(c_356,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_410,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | k1_relat_1(X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_356])).

cnf(c_411,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_411])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_746,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_590])).

cnf(c_764,plain,
    ( ~ v1_relat_1(sK3)
    | sP1_iProver_split
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_746])).

cnf(c_1040,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_1102,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1040,c_751,c_752])).

cnf(c_1152,plain,
    ( ~ v1_relat_1(sK3)
    | sP1_iProver_split
    | k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1102])).

cnf(c_763,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_746])).

cnf(c_1041,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1061,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1041,c_751])).

cnf(c_1224,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1061])).

cnf(c_1225,plain,
    ( ~ sP1_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1224])).

cnf(c_1421,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_20,c_1152,c_1216,c_1225,c_1249])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_754,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1429,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1421,c_754])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k8_relset_1(X1_52,X2_52,X0_52,X2_52) = k1_relset_1(X1_52,X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1032,plain,
    ( k8_relset_1(X0_52,X1_52,X2_52,X1_52) = k1_relset_1(X0_52,X1_52,X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_1391,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1055,c_1032])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_758,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k1_relset_1(X1_52,X2_52,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1031,plain,
    ( k1_relset_1(X0_52,X1_52,X2_52) = k1_relat_1(X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_1387,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1055,c_1031])).

cnf(c_1787,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1391,c_1387])).

cnf(c_18,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_755,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1058,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_755,c_751,c_752])).

cnf(c_1789,plain,
    ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1787,c_1058])).

cnf(c_1840,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1429,c_1789])).

cnf(c_2192,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2188,c_1840])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_179,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_451,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_relat_1(X0)
    | X1 != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_5])).

cnf(c_452,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_365,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_341])).

cnf(c_366,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_389,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK1) != X1
    | k1_relat_1(X0) = X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_366])).

cnf(c_390,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = u1_struct_0(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | sK3 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_452,c_390])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0_52
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_747])).

cnf(c_1039,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_1071,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1039,c_752])).

cnf(c_1425,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1071])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | sK3 != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_390])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1_52)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_608])).

cnf(c_765,plain,
    ( ~ v1_relat_1(sK3)
    | sP1_iProver_split
    | sP0_iProver_split
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_745])).

cnf(c_1042,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_1085,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1042,c_751])).

cnf(c_1283,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1085,c_29,c_1217,c_1224,c_1250])).

cnf(c_2342,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | k1_xboole_0 = X0_52 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1425,c_29,c_1085,c_1217,c_1224,c_1250,c_1789])).

cnf(c_2343,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2342])).

cnf(c_2348,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2192,c_2343])).

cnf(c_1842,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1840,c_1789])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2348,c_1842])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.85/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.00  
% 1.85/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.85/1.00  
% 1.85/1.00  ------  iProver source info
% 1.85/1.00  
% 1.85/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.85/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.85/1.00  git: non_committed_changes: false
% 1.85/1.00  git: last_make_outside_of_git: false
% 1.85/1.00  
% 1.85/1.00  ------ 
% 1.85/1.00  
% 1.85/1.00  ------ Input Options
% 1.85/1.00  
% 1.85/1.00  --out_options                           all
% 1.85/1.00  --tptp_safe_out                         true
% 1.85/1.00  --problem_path                          ""
% 1.85/1.00  --include_path                          ""
% 1.85/1.00  --clausifier                            res/vclausify_rel
% 1.85/1.00  --clausifier_options                    --mode clausify
% 1.85/1.00  --stdin                                 false
% 1.85/1.00  --stats_out                             all
% 1.85/1.00  
% 1.85/1.00  ------ General Options
% 1.85/1.00  
% 1.85/1.00  --fof                                   false
% 1.85/1.00  --time_out_real                         305.
% 1.85/1.00  --time_out_virtual                      -1.
% 1.85/1.00  --symbol_type_check                     false
% 1.85/1.00  --clausify_out                          false
% 1.85/1.00  --sig_cnt_out                           false
% 1.85/1.00  --trig_cnt_out                          false
% 1.85/1.00  --trig_cnt_out_tolerance                1.
% 1.85/1.00  --trig_cnt_out_sk_spl                   false
% 1.85/1.00  --abstr_cl_out                          false
% 1.85/1.00  
% 1.85/1.00  ------ Global Options
% 1.85/1.00  
% 1.85/1.00  --schedule                              default
% 1.85/1.00  --add_important_lit                     false
% 1.85/1.00  --prop_solver_per_cl                    1000
% 1.85/1.00  --min_unsat_core                        false
% 1.85/1.00  --soft_assumptions                      false
% 1.85/1.00  --soft_lemma_size                       3
% 1.85/1.00  --prop_impl_unit_size                   0
% 1.85/1.00  --prop_impl_unit                        []
% 1.85/1.00  --share_sel_clauses                     true
% 1.85/1.00  --reset_solvers                         false
% 1.85/1.00  --bc_imp_inh                            [conj_cone]
% 1.85/1.00  --conj_cone_tolerance                   3.
% 1.85/1.00  --extra_neg_conj                        none
% 1.85/1.00  --large_theory_mode                     true
% 1.85/1.00  --prolific_symb_bound                   200
% 1.85/1.00  --lt_threshold                          2000
% 1.85/1.00  --clause_weak_htbl                      true
% 1.85/1.00  --gc_record_bc_elim                     false
% 1.85/1.00  
% 1.85/1.00  ------ Preprocessing Options
% 1.85/1.00  
% 1.85/1.00  --preprocessing_flag                    true
% 1.85/1.00  --time_out_prep_mult                    0.1
% 1.85/1.00  --splitting_mode                        input
% 1.85/1.00  --splitting_grd                         true
% 1.85/1.00  --splitting_cvd                         false
% 1.85/1.00  --splitting_cvd_svl                     false
% 1.85/1.00  --splitting_nvd                         32
% 1.85/1.00  --sub_typing                            true
% 1.85/1.00  --prep_gs_sim                           true
% 1.85/1.00  --prep_unflatten                        true
% 1.85/1.00  --prep_res_sim                          true
% 1.85/1.00  --prep_upred                            true
% 1.85/1.00  --prep_sem_filter                       exhaustive
% 1.85/1.00  --prep_sem_filter_out                   false
% 1.85/1.00  --pred_elim                             true
% 1.85/1.00  --res_sim_input                         true
% 1.85/1.00  --eq_ax_congr_red                       true
% 1.85/1.00  --pure_diseq_elim                       true
% 1.85/1.00  --brand_transform                       false
% 1.85/1.00  --non_eq_to_eq                          false
% 1.85/1.00  --prep_def_merge                        true
% 1.85/1.00  --prep_def_merge_prop_impl              false
% 1.85/1.00  --prep_def_merge_mbd                    true
% 1.85/1.00  --prep_def_merge_tr_red                 false
% 1.85/1.00  --prep_def_merge_tr_cl                  false
% 1.85/1.00  --smt_preprocessing                     true
% 1.85/1.00  --smt_ac_axioms                         fast
% 1.85/1.00  --preprocessed_out                      false
% 1.85/1.00  --preprocessed_stats                    false
% 1.85/1.00  
% 1.85/1.00  ------ Abstraction refinement Options
% 1.85/1.00  
% 1.85/1.00  --abstr_ref                             []
% 1.85/1.00  --abstr_ref_prep                        false
% 1.85/1.00  --abstr_ref_until_sat                   false
% 1.85/1.00  --abstr_ref_sig_restrict                funpre
% 1.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.00  --abstr_ref_under                       []
% 1.85/1.00  
% 1.85/1.00  ------ SAT Options
% 1.85/1.00  
% 1.85/1.00  --sat_mode                              false
% 1.85/1.00  --sat_fm_restart_options                ""
% 1.85/1.00  --sat_gr_def                            false
% 1.85/1.00  --sat_epr_types                         true
% 1.85/1.00  --sat_non_cyclic_types                  false
% 1.85/1.00  --sat_finite_models                     false
% 1.85/1.00  --sat_fm_lemmas                         false
% 1.85/1.00  --sat_fm_prep                           false
% 1.85/1.00  --sat_fm_uc_incr                        true
% 1.85/1.00  --sat_out_model                         small
% 1.85/1.00  --sat_out_clauses                       false
% 1.85/1.00  
% 1.85/1.00  ------ QBF Options
% 1.85/1.00  
% 1.85/1.00  --qbf_mode                              false
% 1.85/1.00  --qbf_elim_univ                         false
% 1.85/1.00  --qbf_dom_inst                          none
% 1.85/1.00  --qbf_dom_pre_inst                      false
% 1.85/1.00  --qbf_sk_in                             false
% 1.85/1.00  --qbf_pred_elim                         true
% 1.85/1.00  --qbf_split                             512
% 1.85/1.00  
% 1.85/1.00  ------ BMC1 Options
% 1.85/1.00  
% 1.85/1.00  --bmc1_incremental                      false
% 1.85/1.00  --bmc1_axioms                           reachable_all
% 1.85/1.00  --bmc1_min_bound                        0
% 1.85/1.00  --bmc1_max_bound                        -1
% 1.85/1.00  --bmc1_max_bound_default                -1
% 1.85/1.00  --bmc1_symbol_reachability              true
% 1.85/1.00  --bmc1_property_lemmas                  false
% 1.85/1.00  --bmc1_k_induction                      false
% 1.85/1.00  --bmc1_non_equiv_states                 false
% 1.85/1.00  --bmc1_deadlock                         false
% 1.85/1.00  --bmc1_ucm                              false
% 1.85/1.00  --bmc1_add_unsat_core                   none
% 1.85/1.00  --bmc1_unsat_core_children              false
% 1.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.00  --bmc1_out_stat                         full
% 1.85/1.00  --bmc1_ground_init                      false
% 1.85/1.00  --bmc1_pre_inst_next_state              false
% 1.85/1.00  --bmc1_pre_inst_state                   false
% 1.85/1.00  --bmc1_pre_inst_reach_state             false
% 1.85/1.00  --bmc1_out_unsat_core                   false
% 1.85/1.00  --bmc1_aig_witness_out                  false
% 1.85/1.00  --bmc1_verbose                          false
% 1.85/1.00  --bmc1_dump_clauses_tptp                false
% 1.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.00  --bmc1_dump_file                        -
% 1.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.00  --bmc1_ucm_extend_mode                  1
% 1.85/1.00  --bmc1_ucm_init_mode                    2
% 1.85/1.00  --bmc1_ucm_cone_mode                    none
% 1.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.00  --bmc1_ucm_relax_model                  4
% 1.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.00  --bmc1_ucm_layered_model                none
% 1.85/1.00  --bmc1_ucm_max_lemma_size               10
% 1.85/1.00  
% 1.85/1.00  ------ AIG Options
% 1.85/1.00  
% 1.85/1.00  --aig_mode                              false
% 1.85/1.00  
% 1.85/1.00  ------ Instantiation Options
% 1.85/1.00  
% 1.85/1.00  --instantiation_flag                    true
% 1.85/1.00  --inst_sos_flag                         false
% 1.85/1.00  --inst_sos_phase                        true
% 1.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.00  --inst_lit_sel_side                     num_symb
% 1.85/1.00  --inst_solver_per_active                1400
% 1.85/1.00  --inst_solver_calls_frac                1.
% 1.85/1.00  --inst_passive_queue_type               priority_queues
% 1.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.00  --inst_passive_queues_freq              [25;2]
% 1.85/1.00  --inst_dismatching                      true
% 1.85/1.00  --inst_eager_unprocessed_to_passive     true
% 1.85/1.00  --inst_prop_sim_given                   true
% 1.85/1.00  --inst_prop_sim_new                     false
% 1.85/1.00  --inst_subs_new                         false
% 1.85/1.00  --inst_eq_res_simp                      false
% 1.85/1.00  --inst_subs_given                       false
% 1.85/1.00  --inst_orphan_elimination               true
% 1.85/1.00  --inst_learning_loop_flag               true
% 1.85/1.00  --inst_learning_start                   3000
% 1.85/1.00  --inst_learning_factor                  2
% 1.85/1.00  --inst_start_prop_sim_after_learn       3
% 1.85/1.00  --inst_sel_renew                        solver
% 1.85/1.00  --inst_lit_activity_flag                true
% 1.85/1.00  --inst_restr_to_given                   false
% 1.85/1.00  --inst_activity_threshold               500
% 1.85/1.00  --inst_out_proof                        true
% 1.85/1.00  
% 1.85/1.00  ------ Resolution Options
% 1.85/1.00  
% 1.85/1.00  --resolution_flag                       true
% 1.85/1.00  --res_lit_sel                           adaptive
% 1.85/1.00  --res_lit_sel_side                      none
% 1.85/1.00  --res_ordering                          kbo
% 1.85/1.00  --res_to_prop_solver                    active
% 1.85/1.00  --res_prop_simpl_new                    false
% 1.85/1.00  --res_prop_simpl_given                  true
% 1.85/1.00  --res_passive_queue_type                priority_queues
% 1.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.00  --res_passive_queues_freq               [15;5]
% 1.85/1.00  --res_forward_subs                      full
% 1.85/1.00  --res_backward_subs                     full
% 1.85/1.00  --res_forward_subs_resolution           true
% 1.85/1.00  --res_backward_subs_resolution          true
% 1.85/1.00  --res_orphan_elimination                true
% 1.85/1.00  --res_time_limit                        2.
% 1.85/1.00  --res_out_proof                         true
% 1.85/1.00  
% 1.85/1.00  ------ Superposition Options
% 1.85/1.00  
% 1.85/1.00  --superposition_flag                    true
% 1.85/1.00  --sup_passive_queue_type                priority_queues
% 1.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.00  --demod_completeness_check              fast
% 1.85/1.00  --demod_use_ground                      true
% 1.85/1.00  --sup_to_prop_solver                    passive
% 1.85/1.00  --sup_prop_simpl_new                    true
% 1.85/1.00  --sup_prop_simpl_given                  true
% 1.85/1.00  --sup_fun_splitting                     false
% 1.85/1.00  --sup_smt_interval                      50000
% 1.85/1.00  
% 1.85/1.00  ------ Superposition Simplification Setup
% 1.85/1.00  
% 1.85/1.00  --sup_indices_passive                   []
% 1.85/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.00  --sup_full_bw                           [BwDemod]
% 1.85/1.00  --sup_immed_triv                        [TrivRules]
% 1.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.00  --sup_immed_bw_main                     []
% 1.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.00  
% 1.85/1.00  ------ Combination Options
% 1.85/1.00  
% 1.85/1.00  --comb_res_mult                         3
% 1.85/1.00  --comb_sup_mult                         2
% 1.85/1.00  --comb_inst_mult                        10
% 1.85/1.00  
% 1.85/1.00  ------ Debug Options
% 1.85/1.00  
% 1.85/1.00  --dbg_backtrace                         false
% 1.85/1.00  --dbg_dump_prop_clauses                 false
% 1.85/1.00  --dbg_dump_prop_clauses_file            -
% 1.85/1.00  --dbg_out_stat                          false
% 1.85/1.00  ------ Parsing...
% 1.85/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.85/1.00  
% 1.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.85/1.00  
% 1.85/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.85/1.00  
% 1.85/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.85/1.00  ------ Proving...
% 1.85/1.00  ------ Problem Properties 
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  clauses                                 20
% 1.85/1.00  conjectures                             3
% 1.85/1.00  EPR                                     0
% 1.85/1.00  Horn                                    16
% 1.85/1.00  unary                                   5
% 1.85/1.00  binary                                  6
% 1.85/1.00  lits                                    49
% 1.85/1.00  lits eq                                 16
% 1.85/1.00  fd_pure                                 0
% 1.85/1.00  fd_pseudo                               0
% 1.85/1.00  fd_cond                                 2
% 1.85/1.00  fd_pseudo_cond                          0
% 1.85/1.00  AC symbols                              0
% 1.85/1.00  
% 1.85/1.00  ------ Schedule dynamic 5 is on 
% 1.85/1.00  
% 1.85/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  ------ 
% 1.85/1.00  Current options:
% 1.85/1.00  ------ 
% 1.85/1.00  
% 1.85/1.00  ------ Input Options
% 1.85/1.00  
% 1.85/1.00  --out_options                           all
% 1.85/1.00  --tptp_safe_out                         true
% 1.85/1.00  --problem_path                          ""
% 1.85/1.00  --include_path                          ""
% 1.85/1.00  --clausifier                            res/vclausify_rel
% 1.85/1.00  --clausifier_options                    --mode clausify
% 1.85/1.00  --stdin                                 false
% 1.85/1.00  --stats_out                             all
% 1.85/1.00  
% 1.85/1.00  ------ General Options
% 1.85/1.00  
% 1.85/1.00  --fof                                   false
% 1.85/1.00  --time_out_real                         305.
% 1.85/1.00  --time_out_virtual                      -1.
% 1.85/1.00  --symbol_type_check                     false
% 1.85/1.00  --clausify_out                          false
% 1.85/1.00  --sig_cnt_out                           false
% 1.85/1.00  --trig_cnt_out                          false
% 1.85/1.00  --trig_cnt_out_tolerance                1.
% 1.85/1.00  --trig_cnt_out_sk_spl                   false
% 1.85/1.00  --abstr_cl_out                          false
% 1.85/1.00  
% 1.85/1.00  ------ Global Options
% 1.85/1.00  
% 1.85/1.00  --schedule                              default
% 1.85/1.00  --add_important_lit                     false
% 1.85/1.00  --prop_solver_per_cl                    1000
% 1.85/1.00  --min_unsat_core                        false
% 1.85/1.00  --soft_assumptions                      false
% 1.85/1.00  --soft_lemma_size                       3
% 1.85/1.00  --prop_impl_unit_size                   0
% 1.85/1.00  --prop_impl_unit                        []
% 1.85/1.00  --share_sel_clauses                     true
% 1.85/1.00  --reset_solvers                         false
% 1.85/1.00  --bc_imp_inh                            [conj_cone]
% 1.85/1.00  --conj_cone_tolerance                   3.
% 1.85/1.00  --extra_neg_conj                        none
% 1.85/1.00  --large_theory_mode                     true
% 1.85/1.00  --prolific_symb_bound                   200
% 1.85/1.00  --lt_threshold                          2000
% 1.85/1.00  --clause_weak_htbl                      true
% 1.85/1.00  --gc_record_bc_elim                     false
% 1.85/1.00  
% 1.85/1.00  ------ Preprocessing Options
% 1.85/1.00  
% 1.85/1.00  --preprocessing_flag                    true
% 1.85/1.00  --time_out_prep_mult                    0.1
% 1.85/1.00  --splitting_mode                        input
% 1.85/1.00  --splitting_grd                         true
% 1.85/1.00  --splitting_cvd                         false
% 1.85/1.00  --splitting_cvd_svl                     false
% 1.85/1.00  --splitting_nvd                         32
% 1.85/1.00  --sub_typing                            true
% 1.85/1.00  --prep_gs_sim                           true
% 1.85/1.00  --prep_unflatten                        true
% 1.85/1.00  --prep_res_sim                          true
% 1.85/1.00  --prep_upred                            true
% 1.85/1.00  --prep_sem_filter                       exhaustive
% 1.85/1.00  --prep_sem_filter_out                   false
% 1.85/1.00  --pred_elim                             true
% 1.85/1.00  --res_sim_input                         true
% 1.85/1.00  --eq_ax_congr_red                       true
% 1.85/1.00  --pure_diseq_elim                       true
% 1.85/1.00  --brand_transform                       false
% 1.85/1.00  --non_eq_to_eq                          false
% 1.85/1.00  --prep_def_merge                        true
% 1.85/1.00  --prep_def_merge_prop_impl              false
% 1.85/1.00  --prep_def_merge_mbd                    true
% 1.85/1.00  --prep_def_merge_tr_red                 false
% 1.85/1.00  --prep_def_merge_tr_cl                  false
% 1.85/1.00  --smt_preprocessing                     true
% 1.85/1.00  --smt_ac_axioms                         fast
% 1.85/1.00  --preprocessed_out                      false
% 1.85/1.00  --preprocessed_stats                    false
% 1.85/1.00  
% 1.85/1.00  ------ Abstraction refinement Options
% 1.85/1.00  
% 1.85/1.00  --abstr_ref                             []
% 1.85/1.00  --abstr_ref_prep                        false
% 1.85/1.00  --abstr_ref_until_sat                   false
% 1.85/1.00  --abstr_ref_sig_restrict                funpre
% 1.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.00  --abstr_ref_under                       []
% 1.85/1.00  
% 1.85/1.00  ------ SAT Options
% 1.85/1.00  
% 1.85/1.00  --sat_mode                              false
% 1.85/1.00  --sat_fm_restart_options                ""
% 1.85/1.00  --sat_gr_def                            false
% 1.85/1.00  --sat_epr_types                         true
% 1.85/1.00  --sat_non_cyclic_types                  false
% 1.85/1.00  --sat_finite_models                     false
% 1.85/1.00  --sat_fm_lemmas                         false
% 1.85/1.00  --sat_fm_prep                           false
% 1.85/1.00  --sat_fm_uc_incr                        true
% 1.85/1.00  --sat_out_model                         small
% 1.85/1.00  --sat_out_clauses                       false
% 1.85/1.00  
% 1.85/1.00  ------ QBF Options
% 1.85/1.00  
% 1.85/1.00  --qbf_mode                              false
% 1.85/1.00  --qbf_elim_univ                         false
% 1.85/1.00  --qbf_dom_inst                          none
% 1.85/1.00  --qbf_dom_pre_inst                      false
% 1.85/1.00  --qbf_sk_in                             false
% 1.85/1.00  --qbf_pred_elim                         true
% 1.85/1.00  --qbf_split                             512
% 1.85/1.00  
% 1.85/1.00  ------ BMC1 Options
% 1.85/1.00  
% 1.85/1.00  --bmc1_incremental                      false
% 1.85/1.00  --bmc1_axioms                           reachable_all
% 1.85/1.00  --bmc1_min_bound                        0
% 1.85/1.00  --bmc1_max_bound                        -1
% 1.85/1.00  --bmc1_max_bound_default                -1
% 1.85/1.00  --bmc1_symbol_reachability              true
% 1.85/1.00  --bmc1_property_lemmas                  false
% 1.85/1.00  --bmc1_k_induction                      false
% 1.85/1.00  --bmc1_non_equiv_states                 false
% 1.85/1.00  --bmc1_deadlock                         false
% 1.85/1.00  --bmc1_ucm                              false
% 1.85/1.00  --bmc1_add_unsat_core                   none
% 1.85/1.00  --bmc1_unsat_core_children              false
% 1.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.00  --bmc1_out_stat                         full
% 1.85/1.00  --bmc1_ground_init                      false
% 1.85/1.00  --bmc1_pre_inst_next_state              false
% 1.85/1.00  --bmc1_pre_inst_state                   false
% 1.85/1.00  --bmc1_pre_inst_reach_state             false
% 1.85/1.00  --bmc1_out_unsat_core                   false
% 1.85/1.00  --bmc1_aig_witness_out                  false
% 1.85/1.00  --bmc1_verbose                          false
% 1.85/1.00  --bmc1_dump_clauses_tptp                false
% 1.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.00  --bmc1_dump_file                        -
% 1.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.00  --bmc1_ucm_extend_mode                  1
% 1.85/1.00  --bmc1_ucm_init_mode                    2
% 1.85/1.00  --bmc1_ucm_cone_mode                    none
% 1.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.00  --bmc1_ucm_relax_model                  4
% 1.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.00  --bmc1_ucm_layered_model                none
% 1.85/1.00  --bmc1_ucm_max_lemma_size               10
% 1.85/1.00  
% 1.85/1.00  ------ AIG Options
% 1.85/1.00  
% 1.85/1.00  --aig_mode                              false
% 1.85/1.00  
% 1.85/1.00  ------ Instantiation Options
% 1.85/1.00  
% 1.85/1.00  --instantiation_flag                    true
% 1.85/1.00  --inst_sos_flag                         false
% 1.85/1.00  --inst_sos_phase                        true
% 1.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.00  --inst_lit_sel_side                     none
% 1.85/1.00  --inst_solver_per_active                1400
% 1.85/1.00  --inst_solver_calls_frac                1.
% 1.85/1.00  --inst_passive_queue_type               priority_queues
% 1.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.00  --inst_passive_queues_freq              [25;2]
% 1.85/1.00  --inst_dismatching                      true
% 1.85/1.00  --inst_eager_unprocessed_to_passive     true
% 1.85/1.00  --inst_prop_sim_given                   true
% 1.85/1.00  --inst_prop_sim_new                     false
% 1.85/1.00  --inst_subs_new                         false
% 1.85/1.00  --inst_eq_res_simp                      false
% 1.85/1.00  --inst_subs_given                       false
% 1.85/1.00  --inst_orphan_elimination               true
% 1.85/1.00  --inst_learning_loop_flag               true
% 1.85/1.00  --inst_learning_start                   3000
% 1.85/1.00  --inst_learning_factor                  2
% 1.85/1.00  --inst_start_prop_sim_after_learn       3
% 1.85/1.00  --inst_sel_renew                        solver
% 1.85/1.00  --inst_lit_activity_flag                true
% 1.85/1.00  --inst_restr_to_given                   false
% 1.85/1.00  --inst_activity_threshold               500
% 1.85/1.00  --inst_out_proof                        true
% 1.85/1.00  
% 1.85/1.00  ------ Resolution Options
% 1.85/1.00  
% 1.85/1.00  --resolution_flag                       false
% 1.85/1.00  --res_lit_sel                           adaptive
% 1.85/1.00  --res_lit_sel_side                      none
% 1.85/1.00  --res_ordering                          kbo
% 1.85/1.00  --res_to_prop_solver                    active
% 1.85/1.00  --res_prop_simpl_new                    false
% 1.85/1.00  --res_prop_simpl_given                  true
% 1.85/1.00  --res_passive_queue_type                priority_queues
% 1.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.00  --res_passive_queues_freq               [15;5]
% 1.85/1.00  --res_forward_subs                      full
% 1.85/1.00  --res_backward_subs                     full
% 1.85/1.00  --res_forward_subs_resolution           true
% 1.85/1.00  --res_backward_subs_resolution          true
% 1.85/1.00  --res_orphan_elimination                true
% 1.85/1.00  --res_time_limit                        2.
% 1.85/1.00  --res_out_proof                         true
% 1.85/1.00  
% 1.85/1.00  ------ Superposition Options
% 1.85/1.00  
% 1.85/1.00  --superposition_flag                    true
% 1.85/1.00  --sup_passive_queue_type                priority_queues
% 1.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.00  --demod_completeness_check              fast
% 1.85/1.00  --demod_use_ground                      true
% 1.85/1.00  --sup_to_prop_solver                    passive
% 1.85/1.00  --sup_prop_simpl_new                    true
% 1.85/1.00  --sup_prop_simpl_given                  true
% 1.85/1.00  --sup_fun_splitting                     false
% 1.85/1.00  --sup_smt_interval                      50000
% 1.85/1.00  
% 1.85/1.00  ------ Superposition Simplification Setup
% 1.85/1.00  
% 1.85/1.00  --sup_indices_passive                   []
% 1.85/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.00  --sup_full_bw                           [BwDemod]
% 1.85/1.00  --sup_immed_triv                        [TrivRules]
% 1.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.00  --sup_immed_bw_main                     []
% 1.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.00  
% 1.85/1.00  ------ Combination Options
% 1.85/1.00  
% 1.85/1.00  --comb_res_mult                         3
% 1.85/1.00  --comb_sup_mult                         2
% 1.85/1.00  --comb_inst_mult                        10
% 1.85/1.00  
% 1.85/1.00  ------ Debug Options
% 1.85/1.00  
% 1.85/1.00  --dbg_backtrace                         false
% 1.85/1.00  --dbg_dump_prop_clauses                 false
% 1.85/1.00  --dbg_dump_prop_clauses_file            -
% 1.85/1.00  --dbg_out_stat                          false
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  ------ Proving...
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  % SZS status Theorem for theBenchmark.p
% 1.85/1.00  
% 1.85/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.85/1.00  
% 1.85/1.00  fof(f14,conjecture,(
% 1.85/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f15,negated_conjecture,(
% 1.85/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.85/1.00    inference(negated_conjecture,[],[f14])).
% 1.85/1.00  
% 1.85/1.00  fof(f31,plain,(
% 1.85/1.00    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.85/1.00    inference(ennf_transformation,[],[f15])).
% 1.85/1.00  
% 1.85/1.00  fof(f32,plain,(
% 1.85/1.00    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.85/1.00    inference(flattening,[],[f31])).
% 1.85/1.00  
% 1.85/1.00  fof(f40,plain,(
% 1.85/1.00    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.85/1.00    introduced(choice_axiom,[])).
% 1.85/1.00  
% 1.85/1.00  fof(f39,plain,(
% 1.85/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 1.85/1.00    introduced(choice_axiom,[])).
% 1.85/1.00  
% 1.85/1.00  fof(f38,plain,(
% 1.85/1.00    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 1.85/1.00    introduced(choice_axiom,[])).
% 1.85/1.00  
% 1.85/1.00  fof(f41,plain,(
% 1.85/1.00    ((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 1.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f40,f39,f38])).
% 1.85/1.00  
% 1.85/1.00  fof(f64,plain,(
% 1.85/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.85/1.00    inference(cnf_transformation,[],[f41])).
% 1.85/1.00  
% 1.85/1.00  fof(f13,axiom,(
% 1.85/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f30,plain,(
% 1.85/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.85/1.00    inference(ennf_transformation,[],[f13])).
% 1.85/1.00  
% 1.85/1.00  fof(f59,plain,(
% 1.85/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f30])).
% 1.85/1.00  
% 1.85/1.00  fof(f60,plain,(
% 1.85/1.00    l1_struct_0(sK1)),
% 1.85/1.00    inference(cnf_transformation,[],[f41])).
% 1.85/1.00  
% 1.85/1.00  fof(f61,plain,(
% 1.85/1.00    l1_struct_0(sK2)),
% 1.85/1.00    inference(cnf_transformation,[],[f41])).
% 1.85/1.00  
% 1.85/1.00  fof(f7,axiom,(
% 1.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f17,plain,(
% 1.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.85/1.00    inference(pure_predicate_removal,[],[f7])).
% 1.85/1.00  
% 1.85/1.00  fof(f22,plain,(
% 1.85/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.00    inference(ennf_transformation,[],[f17])).
% 1.85/1.00  
% 1.85/1.00  fof(f50,plain,(
% 1.85/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.00    inference(cnf_transformation,[],[f22])).
% 1.85/1.00  
% 1.85/1.00  fof(f2,axiom,(
% 1.85/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f33,plain,(
% 1.85/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.85/1.00    inference(nnf_transformation,[],[f2])).
% 1.85/1.00  
% 1.85/1.00  fof(f44,plain,(
% 1.85/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f33])).
% 1.85/1.00  
% 1.85/1.00  fof(f5,axiom,(
% 1.85/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f21,plain,(
% 1.85/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.85/1.00    inference(ennf_transformation,[],[f5])).
% 1.85/1.00  
% 1.85/1.00  fof(f34,plain,(
% 1.85/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.85/1.00    inference(nnf_transformation,[],[f21])).
% 1.85/1.00  
% 1.85/1.00  fof(f47,plain,(
% 1.85/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f34])).
% 1.85/1.00  
% 1.85/1.00  fof(f4,axiom,(
% 1.85/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f20,plain,(
% 1.85/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.85/1.00    inference(ennf_transformation,[],[f4])).
% 1.85/1.00  
% 1.85/1.00  fof(f46,plain,(
% 1.85/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f20])).
% 1.85/1.00  
% 1.85/1.00  fof(f6,axiom,(
% 1.85/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f49,plain,(
% 1.85/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.85/1.00    inference(cnf_transformation,[],[f6])).
% 1.85/1.00  
% 1.85/1.00  fof(f12,axiom,(
% 1.85/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f28,plain,(
% 1.85/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.85/1.00    inference(ennf_transformation,[],[f12])).
% 1.85/1.00  
% 1.85/1.00  fof(f29,plain,(
% 1.85/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.85/1.00    inference(flattening,[],[f28])).
% 1.85/1.00  
% 1.85/1.00  fof(f37,plain,(
% 1.85/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.85/1.00    inference(nnf_transformation,[],[f29])).
% 1.85/1.00  
% 1.85/1.00  fof(f57,plain,(
% 1.85/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f37])).
% 1.85/1.00  
% 1.85/1.00  fof(f1,axiom,(
% 1.85/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f18,plain,(
% 1.85/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.85/1.00    inference(ennf_transformation,[],[f1])).
% 1.85/1.00  
% 1.85/1.00  fof(f42,plain,(
% 1.85/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f18])).
% 1.85/1.00  
% 1.85/1.00  fof(f11,axiom,(
% 1.85/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f26,plain,(
% 1.85/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.85/1.00    inference(ennf_transformation,[],[f11])).
% 1.85/1.00  
% 1.85/1.00  fof(f27,plain,(
% 1.85/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.85/1.00    inference(flattening,[],[f26])).
% 1.85/1.00  
% 1.85/1.00  fof(f56,plain,(
% 1.85/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f27])).
% 1.85/1.00  
% 1.85/1.00  fof(f63,plain,(
% 1.85/1.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.85/1.00    inference(cnf_transformation,[],[f41])).
% 1.85/1.00  
% 1.85/1.00  fof(f62,plain,(
% 1.85/1.00    v1_funct_1(sK3)),
% 1.85/1.00    inference(cnf_transformation,[],[f41])).
% 1.85/1.00  
% 1.85/1.00  fof(f65,plain,(
% 1.85/1.00    k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)),
% 1.85/1.00    inference(cnf_transformation,[],[f41])).
% 1.85/1.00  
% 1.85/1.00  fof(f9,axiom,(
% 1.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f24,plain,(
% 1.85/1.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.00    inference(ennf_transformation,[],[f9])).
% 1.85/1.00  
% 1.85/1.00  fof(f53,plain,(
% 1.85/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.00    inference(cnf_transformation,[],[f24])).
% 1.85/1.00  
% 1.85/1.00  fof(f8,axiom,(
% 1.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f23,plain,(
% 1.85/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.00    inference(ennf_transformation,[],[f8])).
% 1.85/1.00  
% 1.85/1.00  fof(f51,plain,(
% 1.85/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.00    inference(cnf_transformation,[],[f23])).
% 1.85/1.00  
% 1.85/1.00  fof(f66,plain,(
% 1.85/1.00    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)),
% 1.85/1.00    inference(cnf_transformation,[],[f41])).
% 1.85/1.00  
% 1.85/1.00  fof(f43,plain,(
% 1.85/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.85/1.00    inference(cnf_transformation,[],[f33])).
% 1.85/1.00  
% 1.85/1.00  fof(f48,plain,(
% 1.85/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f34])).
% 1.85/1.00  
% 1.85/1.00  fof(f3,axiom,(
% 1.85/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f19,plain,(
% 1.85/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.85/1.00    inference(ennf_transformation,[],[f3])).
% 1.85/1.00  
% 1.85/1.00  fof(f45,plain,(
% 1.85/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.85/1.00    inference(cnf_transformation,[],[f19])).
% 1.85/1.00  
% 1.85/1.00  fof(f10,axiom,(
% 1.85/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.00  
% 1.85/1.00  fof(f16,plain,(
% 1.85/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.85/1.00    inference(pure_predicate_removal,[],[f10])).
% 1.85/1.00  
% 1.85/1.00  fof(f25,plain,(
% 1.85/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.85/1.00    inference(ennf_transformation,[],[f16])).
% 1.85/1.00  
% 1.85/1.00  fof(f35,plain,(
% 1.85/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.85/1.00    introduced(choice_axiom,[])).
% 1.85/1.00  
% 1.85/1.00  fof(f36,plain,(
% 1.85/1.00    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).
% 1.85/1.00  
% 1.85/1.00  fof(f54,plain,(
% 1.85/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.85/1.00    inference(cnf_transformation,[],[f36])).
% 1.85/1.00  
% 1.85/1.00  cnf(c_20,negated_conjecture,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.85/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_753,negated_conjecture,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1034,plain,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_17,plain,
% 1.85/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.85/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_24,negated_conjecture,
% 1.85/1.00      ( l1_struct_0(sK1) ),
% 1.85/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_314,plain,
% 1.85/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_315,plain,
% 1.85/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_314]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_751,plain,
% 1.85/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_315]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_23,negated_conjecture,
% 1.85/1.00      ( l1_struct_0(sK2) ),
% 1.85/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_309,plain,
% 1.85/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_310,plain,
% 1.85/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_309]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_752,plain,
% 1.85/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_310]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1055,plain,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
% 1.85/1.00      inference(light_normalisation,[status(thm)],[c_1034,c_751,c_752]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_8,plain,
% 1.85/1.00      ( v4_relat_1(X0,X1)
% 1.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.85/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1,plain,
% 1.85/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.85/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_181,plain,
% 1.85/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.85/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_6,plain,
% 1.85/1.00      ( ~ v4_relat_1(X0,X1)
% 1.85/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 1.85/1.00      | ~ v1_relat_1(X0) ),
% 1.85/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_484,plain,
% 1.85/1.00      ( ~ v4_relat_1(X0,X1)
% 1.85/1.00      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 1.85/1.00      | ~ v1_relat_1(X0)
% 1.85/1.00      | X1 != X3
% 1.85/1.00      | k1_relat_1(X0) != X2 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_181,c_6]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_485,plain,
% 1.85/1.00      ( ~ v4_relat_1(X0,X1)
% 1.85/1.00      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 1.85/1.00      | ~ v1_relat_1(X0) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_484]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_521,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.00      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 1.85/1.00      | ~ v1_relat_1(X0) ),
% 1.85/1.00      inference(resolution,[status(thm)],[c_8,c_485]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_750,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.85/1.00      | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52))
% 1.85/1.00      | ~ v1_relat_1(X0_52) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_521]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1035,plain,
% 1.85/1.00      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 1.85/1.00      | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52)) = iProver_top
% 1.85/1.00      | v1_relat_1(X0_52) != iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1643,plain,
% 1.85/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 1.85/1.00      | v1_relat_1(sK3) != iProver_top ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_1055,c_1035]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_29,plain,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_4,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.85/1.00      | ~ v1_relat_1(X1)
% 1.85/1.00      | v1_relat_1(X0) ),
% 1.85/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_760,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 1.85/1.00      | ~ v1_relat_1(X1_52)
% 1.85/1.00      | v1_relat_1(X0_52) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1179,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.85/1.00      | v1_relat_1(X0_52)
% 1.85/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1_52,X2_52)) ),
% 1.85/1.00      inference(instantiation,[status(thm)],[c_760]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1216,plain,
% 1.85/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.85/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
% 1.85/1.00      | v1_relat_1(sK3) ),
% 1.85/1.00      inference(instantiation,[status(thm)],[c_1179]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1217,plain,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 1.85/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
% 1.85/1.00      | v1_relat_1(sK3) = iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_7,plain,
% 1.85/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.85/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_759,plain,
% 1.85/1.00      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1249,plain,
% 1.85/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 1.85/1.00      inference(instantiation,[status(thm)],[c_759]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1250,plain,
% 1.85/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_2188,plain,
% 1.85/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 1.85/1.00      inference(global_propositional_subsumption,
% 1.85/1.00                [status(thm)],
% 1.85/1.00                [c_1643,c_29,c_1217,c_1250]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_16,plain,
% 1.85/1.00      ( ~ v1_partfun1(X0,X1)
% 1.85/1.00      | ~ v4_relat_1(X0,X1)
% 1.85/1.00      | ~ v1_relat_1(X0)
% 1.85/1.00      | k1_relat_1(X0) = X1 ),
% 1.85/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_0,plain,
% 1.85/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_13,plain,
% 1.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.85/1.00      | v1_partfun1(X0,X1)
% 1.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.00      | ~ v1_funct_1(X0)
% 1.85/1.00      | v1_xboole_0(X2) ),
% 1.85/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_21,negated_conjecture,
% 1.85/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 1.85/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_338,plain,
% 1.85/1.00      ( v1_partfun1(X0,X1)
% 1.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.00      | ~ v1_funct_1(X0)
% 1.85/1.00      | v1_xboole_0(X2)
% 1.85/1.00      | u1_struct_0(sK2) != X2
% 1.85/1.00      | u1_struct_0(sK1) != X1
% 1.85/1.00      | sK3 != X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_339,plain,
% 1.85/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.85/1.00      | ~ v1_funct_1(sK3)
% 1.85/1.00      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_22,negated_conjecture,
% 1.85/1.00      ( v1_funct_1(sK3) ),
% 1.85/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_341,plain,
% 1.85/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.85/1.00      inference(global_propositional_subsumption,
% 1.85/1.00                [status(thm)],
% 1.85/1.00                [c_339,c_22,c_20]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_355,plain,
% 1.85/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | u1_struct_0(sK2) != X0
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_341]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_356,plain,
% 1.85/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | k1_xboole_0 = u1_struct_0(sK2) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_410,plain,
% 1.85/1.00      ( ~ v4_relat_1(X0,X1)
% 1.85/1.00      | ~ v1_relat_1(X0)
% 1.85/1.00      | u1_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | u1_struct_0(sK1) != X1
% 1.85/1.00      | k1_relat_1(X0) = X1
% 1.85/1.00      | sK3 != X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_356]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_411,plain,
% 1.85/1.00      ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_410]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_589,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | u1_struct_0(sK1) != X1
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | sK3 != X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_411]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_590,plain,
% 1.85/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_589]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_746,plain,
% 1.85/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_590]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_764,plain,
% 1.85/1.00      ( ~ v1_relat_1(sK3)
% 1.85/1.00      | sP1_iProver_split
% 1.85/1.00      | u1_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(splitting,
% 1.85/1.00                [splitting(split),new_symbols(definition,[])],
% 1.85/1.00                [c_746]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1040,plain,
% 1.85/1.00      ( u1_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | v1_relat_1(sK3) != iProver_top
% 1.85/1.00      | sP1_iProver_split = iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1102,plain,
% 1.85/1.00      ( k2_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | v1_relat_1(sK3) != iProver_top
% 1.85/1.00      | sP1_iProver_split = iProver_top ),
% 1.85/1.00      inference(demodulation,[status(thm)],[c_1040,c_751,c_752]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1152,plain,
% 1.85/1.00      ( ~ v1_relat_1(sK3)
% 1.85/1.00      | sP1_iProver_split
% 1.85/1.00      | k2_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1102]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_763,plain,
% 1.85/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
% 1.85/1.00      | ~ sP1_iProver_split ),
% 1.85/1.00      inference(splitting,
% 1.85/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.85/1.00                [c_746]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1041,plain,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52))) != iProver_top
% 1.85/1.00      | sP1_iProver_split != iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1061,plain,
% 1.85/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top
% 1.85/1.00      | sP1_iProver_split != iProver_top ),
% 1.85/1.00      inference(light_normalisation,[status(thm)],[c_1041,c_751]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1224,plain,
% 1.85/1.00      ( sP1_iProver_split != iProver_top ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_1055,c_1061]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1225,plain,
% 1.85/1.00      ( ~ sP1_iProver_split ),
% 1.85/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1224]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1421,plain,
% 1.85/1.00      ( k2_struct_0(sK2) = k1_xboole_0
% 1.85/1.00      | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(global_propositional_subsumption,
% 1.85/1.00                [status(thm)],
% 1.85/1.00                [c_1102,c_20,c_1152,c_1216,c_1225,c_1249]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_19,negated_conjecture,
% 1.85/1.00      ( k1_xboole_0 != k2_struct_0(sK2)
% 1.85/1.00      | k1_xboole_0 = k2_struct_0(sK1) ),
% 1.85/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_754,negated_conjecture,
% 1.85/1.00      ( k1_xboole_0 != k2_struct_0(sK2)
% 1.85/1.00      | k1_xboole_0 = k2_struct_0(sK1) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1429,plain,
% 1.85/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_1421,c_754]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_10,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 1.85/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_757,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.85/1.00      | k8_relset_1(X1_52,X2_52,X0_52,X2_52) = k1_relset_1(X1_52,X2_52,X0_52) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1032,plain,
% 1.85/1.00      ( k8_relset_1(X0_52,X1_52,X2_52,X1_52) = k1_relset_1(X0_52,X1_52,X2_52)
% 1.85/1.00      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1391,plain,
% 1.85/1.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_1055,c_1032]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_9,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.85/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_758,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.85/1.00      | k1_relset_1(X1_52,X2_52,X0_52) = k1_relat_1(X0_52) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1031,plain,
% 1.85/1.00      ( k1_relset_1(X0_52,X1_52,X2_52) = k1_relat_1(X2_52)
% 1.85/1.00      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1387,plain,
% 1.85/1.00      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_1055,c_1031]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1787,plain,
% 1.85/1.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(light_normalisation,[status(thm)],[c_1391,c_1387]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_18,negated_conjecture,
% 1.85/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.85/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_755,negated_conjecture,
% 1.85/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1058,plain,
% 1.85/1.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.85/1.00      inference(light_normalisation,[status(thm)],[c_755,c_751,c_752]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1789,plain,
% 1.85/1.00      ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 1.85/1.00      inference(demodulation,[status(thm)],[c_1787,c_1058]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1840,plain,
% 1.85/1.00      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_1429,c_1789]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_2192,plain,
% 1.85/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.85/1.00      inference(light_normalisation,[status(thm)],[c_2188,c_1840]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_2,plain,
% 1.85/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.85/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_179,plain,
% 1.85/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.85/1.00      inference(prop_impl,[status(thm)],[c_2]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_5,plain,
% 1.85/1.00      ( v4_relat_1(X0,X1)
% 1.85/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.85/1.00      | ~ v1_relat_1(X0) ),
% 1.85/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_451,plain,
% 1.85/1.00      ( v4_relat_1(X0,X1)
% 1.85/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 1.85/1.00      | ~ v1_relat_1(X0)
% 1.85/1.00      | X1 != X3
% 1.85/1.00      | k1_relat_1(X0) != X2 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_179,c_5]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_452,plain,
% 1.85/1.00      ( v4_relat_1(X0,X1)
% 1.85/1.00      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 1.85/1.00      | ~ v1_relat_1(X0) ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_451]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_3,plain,
% 1.85/1.00      ( ~ r2_hidden(X0,X1)
% 1.85/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.85/1.00      | ~ v1_xboole_0(X2) ),
% 1.85/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_12,plain,
% 1.85/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_321,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.85/1.00      | ~ v1_xboole_0(X1)
% 1.85/1.00      | X2 != X0
% 1.85/1.00      | sK0(X2) != X3
% 1.85/1.00      | k1_xboole_0 = X2 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_322,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.85/1.00      | ~ v1_xboole_0(X1)
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_321]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_365,plain,
% 1.85/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.85/1.00      | u1_struct_0(sK2) != X1
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_322,c_341]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_366,plain,
% 1.85/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_389,plain,
% 1.85/1.00      ( ~ v4_relat_1(X0,X1)
% 1.85/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ v1_relat_1(X0)
% 1.85/1.00      | u1_struct_0(sK1) != X1
% 1.85/1.00      | k1_relat_1(X0) = X1
% 1.85/1.00      | sK3 != X0
% 1.85/1.00      | k1_xboole_0 = X2 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_366]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_390,plain,
% 1.85/1.00      ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
% 1.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | k1_relat_1(sK3) = u1_struct_0(sK1)
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_389]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_568,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
% 1.85/1.00      | ~ v1_relat_1(X1)
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK1) != X2
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | sK3 != X1
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_452,c_390]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_569,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_568]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_747,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | k1_xboole_0 = X0_52 ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_569]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_761,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | k1_xboole_0 = X0_52
% 1.85/1.00      | ~ sP0_iProver_split ),
% 1.85/1.00      inference(splitting,
% 1.85/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.85/1.00                [c_747]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1039,plain,
% 1.85/1.00      ( k1_xboole_0 = X0_52
% 1.85/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.85/1.00      | sP0_iProver_split != iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1071,plain,
% 1.85/1.00      ( k1_xboole_0 = X0_52
% 1.85/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.85/1.00      | sP0_iProver_split != iProver_top ),
% 1.85/1.00      inference(light_normalisation,[status(thm)],[c_1039,c_752]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1425,plain,
% 1.85/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | k1_xboole_0 = X0_52
% 1.85/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.85/1.00      | sP0_iProver_split != iProver_top ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_1421,c_1071]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_607,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK1) != X1
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | sK3 != X0
% 1.85/1.00      | k1_xboole_0 = X3 ),
% 1.85/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_390]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_608,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | k1_xboole_0 = X0 ),
% 1.85/1.00      inference(unflattening,[status(thm)],[c_607]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_745,plain,
% 1.85/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1_52)))
% 1.85/1.00      | ~ v1_relat_1(sK3)
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | k1_xboole_0 = X0_52 ),
% 1.85/1.00      inference(subtyping,[status(esa)],[c_608]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_765,plain,
% 1.85/1.00      ( ~ v1_relat_1(sK3)
% 1.85/1.00      | sP1_iProver_split
% 1.85/1.00      | sP0_iProver_split
% 1.85/1.00      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.85/1.00      inference(splitting,
% 1.85/1.00                [splitting(split),new_symbols(definition,[])],
% 1.85/1.00                [c_745]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1042,plain,
% 1.85/1.00      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | v1_relat_1(sK3) != iProver_top
% 1.85/1.00      | sP1_iProver_split = iProver_top
% 1.85/1.00      | sP0_iProver_split = iProver_top ),
% 1.85/1.00      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1085,plain,
% 1.85/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | v1_relat_1(sK3) != iProver_top
% 1.85/1.00      | sP1_iProver_split = iProver_top
% 1.85/1.00      | sP0_iProver_split = iProver_top ),
% 1.85/1.00      inference(demodulation,[status(thm)],[c_1042,c_751]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1283,plain,
% 1.85/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.85/1.00      | sP0_iProver_split = iProver_top ),
% 1.85/1.00      inference(global_propositional_subsumption,
% 1.85/1.00                [status(thm)],
% 1.85/1.00                [c_1085,c_29,c_1217,c_1224,c_1250]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_2342,plain,
% 1.85/1.00      ( m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.85/1.00      | k1_xboole_0 = X0_52 ),
% 1.85/1.00      inference(global_propositional_subsumption,
% 1.85/1.00                [status(thm)],
% 1.85/1.00                [c_1425,c_29,c_1085,c_1217,c_1224,c_1250,c_1789]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_2343,plain,
% 1.85/1.00      ( k1_xboole_0 = X0_52
% 1.85/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.85/1.00      inference(renaming,[status(thm)],[c_2342]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_2348,plain,
% 1.85/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.85/1.00      inference(superposition,[status(thm)],[c_2192,c_2343]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(c_1842,plain,
% 1.85/1.00      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 1.85/1.00      inference(demodulation,[status(thm)],[c_1840,c_1789]) ).
% 1.85/1.00  
% 1.85/1.00  cnf(contradiction,plain,
% 1.85/1.00      ( $false ),
% 1.85/1.00      inference(minisat,[status(thm)],[c_2348,c_1842]) ).
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.85/1.00  
% 1.85/1.00  ------                               Statistics
% 1.85/1.00  
% 1.85/1.00  ------ General
% 1.85/1.00  
% 1.85/1.00  abstr_ref_over_cycles:                  0
% 1.85/1.00  abstr_ref_under_cycles:                 0
% 1.85/1.00  gc_basic_clause_elim:                   0
% 1.85/1.00  forced_gc_time:                         0
% 1.85/1.00  parsing_time:                           0.009
% 1.85/1.00  unif_index_cands_time:                  0.
% 1.85/1.00  unif_index_add_time:                    0.
% 1.85/1.00  orderings_time:                         0.
% 1.85/1.00  out_proof_time:                         0.014
% 1.85/1.00  total_time:                             0.104
% 1.85/1.00  num_of_symbols:                         61
% 1.85/1.00  num_of_terms:                           1667
% 1.85/1.00  
% 1.85/1.00  ------ Preprocessing
% 1.85/1.00  
% 1.85/1.00  num_of_splits:                          4
% 1.85/1.00  num_of_split_atoms:                     2
% 1.85/1.00  num_of_reused_defs:                     2
% 1.85/1.00  num_eq_ax_congr_red:                    39
% 1.85/1.00  num_of_sem_filtered_clauses:            4
% 1.85/1.00  num_of_subtypes:                        4
% 1.85/1.00  monotx_restored_types:                  0
% 1.85/1.00  sat_num_of_epr_types:                   0
% 1.85/1.00  sat_num_of_non_cyclic_types:            0
% 1.85/1.00  sat_guarded_non_collapsed_types:        1
% 1.85/1.00  num_pure_diseq_elim:                    0
% 1.85/1.00  simp_replaced_by:                       0
% 1.85/1.00  res_preprocessed:                       96
% 1.85/1.00  prep_upred:                             0
% 1.85/1.00  prep_unflattend:                        29
% 1.85/1.00  smt_new_axioms:                         0
% 1.85/1.00  pred_elim_cands:                        2
% 1.85/1.00  pred_elim:                              8
% 1.85/1.00  pred_elim_cl:                           8
% 1.85/1.00  pred_elim_cycles:                       10
% 1.85/1.00  merged_defs:                            2
% 1.85/1.00  merged_defs_ncl:                        0
% 1.85/1.00  bin_hyper_res:                          3
% 1.85/1.00  prep_cycles:                            4
% 1.85/1.00  pred_elim_time:                         0.008
% 1.85/1.00  splitting_time:                         0.
% 1.85/1.00  sem_filter_time:                        0.
% 1.85/1.00  monotx_time:                            0.
% 1.85/1.00  subtype_inf_time:                       0.
% 1.85/1.00  
% 1.85/1.00  ------ Problem properties
% 1.85/1.00  
% 1.85/1.00  clauses:                                20
% 1.85/1.00  conjectures:                            3
% 1.85/1.00  epr:                                    0
% 1.85/1.00  horn:                                   16
% 1.85/1.00  ground:                                 9
% 1.85/1.00  unary:                                  5
% 1.85/1.00  binary:                                 6
% 1.85/1.00  lits:                                   49
% 1.85/1.00  lits_eq:                                16
% 1.85/1.00  fd_pure:                                0
% 1.85/1.00  fd_pseudo:                              0
% 1.85/1.00  fd_cond:                                2
% 1.85/1.00  fd_pseudo_cond:                         0
% 1.85/1.00  ac_symbols:                             0
% 1.85/1.00  
% 1.85/1.00  ------ Propositional Solver
% 1.85/1.00  
% 1.85/1.00  prop_solver_calls:                      30
% 1.85/1.00  prop_fast_solver_calls:                 633
% 1.85/1.00  smt_solver_calls:                       0
% 1.85/1.00  smt_fast_solver_calls:                  0
% 1.85/1.00  prop_num_of_clauses:                    717
% 1.85/1.00  prop_preprocess_simplified:             3010
% 1.85/1.00  prop_fo_subsumed:                       18
% 1.85/1.00  prop_solver_time:                       0.
% 1.85/1.00  smt_solver_time:                        0.
% 1.85/1.00  smt_fast_solver_time:                   0.
% 1.85/1.00  prop_fast_solver_time:                  0.
% 1.85/1.00  prop_unsat_core_time:                   0.
% 1.85/1.00  
% 1.85/1.00  ------ QBF
% 1.85/1.00  
% 1.85/1.00  qbf_q_res:                              0
% 1.85/1.00  qbf_num_tautologies:                    0
% 1.85/1.00  qbf_prep_cycles:                        0
% 1.85/1.00  
% 1.85/1.00  ------ BMC1
% 1.85/1.00  
% 1.85/1.00  bmc1_current_bound:                     -1
% 1.85/1.00  bmc1_last_solved_bound:                 -1
% 1.85/1.00  bmc1_unsat_core_size:                   -1
% 1.85/1.00  bmc1_unsat_core_parents_size:           -1
% 1.85/1.00  bmc1_merge_next_fun:                    0
% 1.85/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.85/1.00  
% 1.85/1.00  ------ Instantiation
% 1.85/1.00  
% 1.85/1.00  inst_num_of_clauses:                    254
% 1.85/1.00  inst_num_in_passive:                    95
% 1.85/1.00  inst_num_in_active:                     132
% 1.85/1.00  inst_num_in_unprocessed:                27
% 1.85/1.00  inst_num_of_loops:                      170
% 1.85/1.00  inst_num_of_learning_restarts:          0
% 1.85/1.00  inst_num_moves_active_passive:          32
% 1.85/1.00  inst_lit_activity:                      0
% 1.85/1.00  inst_lit_activity_moves:                0
% 1.85/1.00  inst_num_tautologies:                   0
% 1.85/1.00  inst_num_prop_implied:                  0
% 1.85/1.00  inst_num_existing_simplified:           0
% 1.85/1.00  inst_num_eq_res_simplified:             0
% 1.85/1.00  inst_num_child_elim:                    0
% 1.85/1.00  inst_num_of_dismatching_blockings:      49
% 1.85/1.00  inst_num_of_non_proper_insts:           199
% 1.85/1.00  inst_num_of_duplicates:                 0
% 1.85/1.00  inst_inst_num_from_inst_to_res:         0
% 1.85/1.00  inst_dismatching_checking_time:         0.
% 1.85/1.00  
% 1.85/1.00  ------ Resolution
% 1.85/1.00  
% 1.85/1.00  res_num_of_clauses:                     0
% 1.85/1.00  res_num_in_passive:                     0
% 1.85/1.00  res_num_in_active:                      0
% 1.85/1.00  res_num_of_loops:                       100
% 1.85/1.00  res_forward_subset_subsumed:            40
% 1.85/1.00  res_backward_subset_subsumed:           0
% 1.85/1.00  res_forward_subsumed:                   1
% 1.85/1.00  res_backward_subsumed:                  0
% 1.85/1.00  res_forward_subsumption_resolution:     0
% 1.85/1.00  res_backward_subsumption_resolution:    0
% 1.85/1.00  res_clause_to_clause_subsumption:       66
% 1.85/1.00  res_orphan_elimination:                 0
% 1.85/1.00  res_tautology_del:                      49
% 1.85/1.00  res_num_eq_res_simplified:              0
% 1.85/1.00  res_num_sel_changes:                    0
% 1.85/1.00  res_moves_from_active_to_pass:          0
% 1.85/1.00  
% 1.85/1.00  ------ Superposition
% 1.85/1.00  
% 1.85/1.00  sup_time_total:                         0.
% 1.85/1.00  sup_time_generating:                    0.
% 1.85/1.00  sup_time_sim_full:                      0.
% 1.85/1.00  sup_time_sim_immed:                     0.
% 1.85/1.00  
% 1.85/1.00  sup_num_of_clauses:                     25
% 1.85/1.00  sup_num_in_active:                      19
% 1.85/1.00  sup_num_in_passive:                     6
% 1.85/1.00  sup_num_of_loops:                       32
% 1.85/1.00  sup_fw_superposition:                   19
% 1.85/1.00  sup_bw_superposition:                   13
% 1.85/1.00  sup_immediate_simplified:               12
% 1.85/1.00  sup_given_eliminated:                   0
% 1.85/1.00  comparisons_done:                       0
% 1.85/1.00  comparisons_avoided:                    6
% 1.85/1.00  
% 1.85/1.00  ------ Simplifications
% 1.85/1.00  
% 1.85/1.00  
% 1.85/1.00  sim_fw_subset_subsumed:                 5
% 1.85/1.00  sim_bw_subset_subsumed:                 4
% 1.85/1.00  sim_fw_subsumed:                        0
% 1.85/1.00  sim_bw_subsumed:                        0
% 1.85/1.00  sim_fw_subsumption_res:                 0
% 1.85/1.00  sim_bw_subsumption_res:                 3
% 1.85/1.00  sim_tautology_del:                      0
% 1.85/1.00  sim_eq_tautology_del:                   3
% 1.85/1.00  sim_eq_res_simp:                        0
% 1.85/1.00  sim_fw_demodulated:                     4
% 1.85/1.00  sim_bw_demodulated:                     17
% 1.85/1.00  sim_light_normalised:                   14
% 1.85/1.00  sim_joinable_taut:                      0
% 1.85/1.00  sim_joinable_simp:                      0
% 1.85/1.00  sim_ac_normalised:                      0
% 1.85/1.00  sim_smt_subsumption:                    0
% 1.85/1.00  
%------------------------------------------------------------------------------
