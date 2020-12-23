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
% DateTime   : Thu Dec  3 12:07:05 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  209 (6171 expanded)
%              Number of clauses        :  141 (1754 expanded)
%              Number of leaves         :   16 (1541 expanded)
%              Depth                    :   27
%              Number of atoms          :  741 (43723 expanded)
%              Number of equality atoms :  351 (3492 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f45,f44])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f77,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k1_xboole_0 != k2_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k1_xboole_0 != k2_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k2_relat_1(X1)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1653,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1648,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1666,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3449,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1648,c_1666])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_331,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_17])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_343,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_331,c_6])).

cnf(c_1644,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_2701,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1644])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1983,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | v2_funct_2(sK1,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1985,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_2221,plain,
    ( ~ v2_funct_2(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relat_1(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_2223,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_2221])).

cnf(c_3324,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_33,c_31,c_30,c_1985,c_2223])).

cnf(c_3461,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3449,c_3324])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1655,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3551,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_1655])).

cnf(c_34,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1958,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1959,plain,
    ( v3_funct_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1958])).

cnf(c_1961,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_4130,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3551,c_34,c_35,c_36,c_37,c_1961])).

cnf(c_4131,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4130])).

cnf(c_4142,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_4131])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4143,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4142])).

cnf(c_4268,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4142,c_38,c_39,c_41])).

cnf(c_4269,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4268])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1656,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7383,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1656])).

cnf(c_2032,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2034,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_7621,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7383,c_33,c_32,c_31,c_30,c_2034])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1654,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7626,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7621,c_1654])).

cnf(c_7768,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4269,c_7626])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1124,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1151,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1947,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1948,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_2186,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1130,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_2105,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X2 != sK2
    | X3 != sK2
    | X0 != sK0
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_2607,plain,
    ( r2_relset_1(X0,X1,sK2,X2)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X2 != sK2
    | X0 != sK0
    | X1 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_7281,plain,
    ( r2_relset_1(X0,X1,sK2,k2_funct_1(sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X0 != sK0
    | X1 != sK0
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2607])).

cnf(c_7287,plain,
    ( X0 != sK0
    | X1 != sK0
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2
    | r2_relset_1(X0,X1,sK2,k2_funct_1(sK1)) = iProver_top
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7281])).

cnf(c_7289,plain,
    ( k2_funct_1(sK1) != sK2
    | sK2 != sK2
    | sK0 != sK0
    | r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) = iProver_top
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7287])).

cnf(c_8737,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7768,c_41,c_1151,c_1948,c_2186,c_4269,c_7289,c_7626])).

cnf(c_1652,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7382,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1656])).

cnf(c_27,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2027,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2029,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_7609,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7382,c_29,c_28,c_27,c_26,c_2029])).

cnf(c_8746,plain,
    ( k2_funct_2(k1_xboole_0,sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_8737,c_7609])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1660,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1663,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | v2_funct_2(X0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7977,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) != iProver_top
    | v2_funct_2(k2_funct_2(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_1663])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_50,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_56,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10681,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v2_funct_2(k2_funct_2(X1,X0),X1) = iProver_top
    | v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7977,c_50,c_56])).

cnf(c_10682,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v2_funct_2(k2_funct_2(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10681])).

cnf(c_10693,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v3_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v2_funct_2(k2_funct_2(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_10682])).

cnf(c_10733,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | v2_funct_2(k2_funct_1(sK2),k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8746,c_10693])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1651,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8767,plain,
    ( v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8737,c_1651])).

cnf(c_1650,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8768,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8737,c_1650])).

cnf(c_8765,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8737,c_1652])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8783,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8765,c_1])).

cnf(c_11178,plain,
    ( v2_funct_2(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10733,c_38,c_8767,c_8768,c_8783])).

cnf(c_7970,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7609,c_1660])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_40,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9657,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7970,c_38,c_39,c_40,c_41])).

cnf(c_9661,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9657,c_8737])).

cnf(c_9662,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9661,c_1])).

cnf(c_2703,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1644])).

cnf(c_9674,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = X0
    | v2_funct_2(k2_funct_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9662,c_2703])).

cnf(c_11430,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11178,c_9674])).

cnf(c_2700,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1644])).

cnf(c_1978,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | v2_funct_2(sK2,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1980,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_2202,plain,
    ( ~ v2_funct_2(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relat_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_2204,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_3154,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2700,c_29,c_27,c_26,c_1980,c_2204])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k2_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1668,plain,
    ( X0 = X1
    | k2_relat_1(X1) != k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4334,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK2 = X0
    | sK0 != k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_1668])).

cnf(c_1921,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1922,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1921])).

cnf(c_4363,plain,
    ( v1_relat_1(X0) != iProver_top
    | sK0 != k1_xboole_0
    | sK2 = X0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4334,c_41,c_1922])).

cnf(c_4364,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK2 = X0
    | sK0 != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4363])).

cnf(c_8753,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK2 = X0
    | k1_xboole_0 != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8737,c_4364])).

cnf(c_8803,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK2 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8753])).

cnf(c_11615,plain,
    ( k2_funct_1(sK2) = sK2
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11430,c_8803])).

cnf(c_1667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7979,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_1667])).

cnf(c_8560,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_2(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_7979])).

cnf(c_8577,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8560,c_7609])).

cnf(c_12960,plain,
    ( k2_funct_1(sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11615,c_38,c_39,c_40,c_8577])).

cnf(c_8744,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8737,c_7626])).

cnf(c_4374,plain,
    ( sK1 = sK2
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_4364])).

cnf(c_1924,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1925,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_4425,plain,
    ( sK0 != k1_xboole_0
    | sK1 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4374,c_37,c_1925])).

cnf(c_4426,plain,
    ( sK1 = sK2
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4425])).

cnf(c_8752,plain,
    ( sK1 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8737,c_4426])).

cnf(c_8810,plain,
    ( sK1 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_8752])).

cnf(c_8837,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8744,c_8810])).

cnf(c_12984,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12960,c_8837])).

cnf(c_1665,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2997,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1665])).

cnf(c_8763,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8737,c_2997])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12984,c_8763])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:36:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.44/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/0.99  
% 3.44/0.99  ------  iProver source info
% 3.44/0.99  
% 3.44/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.44/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/0.99  git: non_committed_changes: false
% 3.44/0.99  git: last_make_outside_of_git: false
% 3.44/0.99  
% 3.44/0.99  ------ 
% 3.44/0.99  
% 3.44/0.99  ------ Input Options
% 3.44/0.99  
% 3.44/0.99  --out_options                           all
% 3.44/0.99  --tptp_safe_out                         true
% 3.44/0.99  --problem_path                          ""
% 3.44/0.99  --include_path                          ""
% 3.44/0.99  --clausifier                            res/vclausify_rel
% 3.44/0.99  --clausifier_options                    --mode clausify
% 3.44/0.99  --stdin                                 false
% 3.44/0.99  --stats_out                             all
% 3.44/0.99  
% 3.44/0.99  ------ General Options
% 3.44/0.99  
% 3.44/0.99  --fof                                   false
% 3.44/0.99  --time_out_real                         305.
% 3.44/0.99  --time_out_virtual                      -1.
% 3.44/0.99  --symbol_type_check                     false
% 3.44/0.99  --clausify_out                          false
% 3.44/0.99  --sig_cnt_out                           false
% 3.44/0.99  --trig_cnt_out                          false
% 3.44/0.99  --trig_cnt_out_tolerance                1.
% 3.44/0.99  --trig_cnt_out_sk_spl                   false
% 3.44/0.99  --abstr_cl_out                          false
% 3.44/0.99  
% 3.44/0.99  ------ Global Options
% 3.44/0.99  
% 3.44/0.99  --schedule                              default
% 3.44/0.99  --add_important_lit                     false
% 3.44/0.99  --prop_solver_per_cl                    1000
% 3.44/0.99  --min_unsat_core                        false
% 3.44/0.99  --soft_assumptions                      false
% 3.44/0.99  --soft_lemma_size                       3
% 3.44/0.99  --prop_impl_unit_size                   0
% 3.44/0.99  --prop_impl_unit                        []
% 3.44/0.99  --share_sel_clauses                     true
% 3.44/0.99  --reset_solvers                         false
% 3.44/0.99  --bc_imp_inh                            [conj_cone]
% 3.44/0.99  --conj_cone_tolerance                   3.
% 3.44/0.99  --extra_neg_conj                        none
% 3.44/0.99  --large_theory_mode                     true
% 3.44/0.99  --prolific_symb_bound                   200
% 3.44/0.99  --lt_threshold                          2000
% 3.44/0.99  --clause_weak_htbl                      true
% 3.44/0.99  --gc_record_bc_elim                     false
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing Options
% 3.44/0.99  
% 3.44/0.99  --preprocessing_flag                    true
% 3.44/0.99  --time_out_prep_mult                    0.1
% 3.44/0.99  --splitting_mode                        input
% 3.44/0.99  --splitting_grd                         true
% 3.44/0.99  --splitting_cvd                         false
% 3.44/0.99  --splitting_cvd_svl                     false
% 3.44/0.99  --splitting_nvd                         32
% 3.44/0.99  --sub_typing                            true
% 3.44/0.99  --prep_gs_sim                           true
% 3.44/0.99  --prep_unflatten                        true
% 3.44/0.99  --prep_res_sim                          true
% 3.44/0.99  --prep_upred                            true
% 3.44/0.99  --prep_sem_filter                       exhaustive
% 3.44/0.99  --prep_sem_filter_out                   false
% 3.44/0.99  --pred_elim                             true
% 3.44/0.99  --res_sim_input                         true
% 3.44/0.99  --eq_ax_congr_red                       true
% 3.44/0.99  --pure_diseq_elim                       true
% 3.44/0.99  --brand_transform                       false
% 3.44/0.99  --non_eq_to_eq                          false
% 3.44/0.99  --prep_def_merge                        true
% 3.44/0.99  --prep_def_merge_prop_impl              false
% 3.44/0.99  --prep_def_merge_mbd                    true
% 3.44/0.99  --prep_def_merge_tr_red                 false
% 3.44/0.99  --prep_def_merge_tr_cl                  false
% 3.44/0.99  --smt_preprocessing                     true
% 3.44/0.99  --smt_ac_axioms                         fast
% 3.44/0.99  --preprocessed_out                      false
% 3.44/0.99  --preprocessed_stats                    false
% 3.44/0.99  
% 3.44/0.99  ------ Abstraction refinement Options
% 3.44/0.99  
% 3.44/0.99  --abstr_ref                             []
% 3.44/0.99  --abstr_ref_prep                        false
% 3.44/0.99  --abstr_ref_until_sat                   false
% 3.44/0.99  --abstr_ref_sig_restrict                funpre
% 3.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/0.99  --abstr_ref_under                       []
% 3.44/0.99  
% 3.44/0.99  ------ SAT Options
% 3.44/0.99  
% 3.44/0.99  --sat_mode                              false
% 3.44/0.99  --sat_fm_restart_options                ""
% 3.44/0.99  --sat_gr_def                            false
% 3.44/0.99  --sat_epr_types                         true
% 3.44/0.99  --sat_non_cyclic_types                  false
% 3.44/0.99  --sat_finite_models                     false
% 3.44/0.99  --sat_fm_lemmas                         false
% 3.44/0.99  --sat_fm_prep                           false
% 3.44/0.99  --sat_fm_uc_incr                        true
% 3.44/0.99  --sat_out_model                         small
% 3.44/0.99  --sat_out_clauses                       false
% 3.44/0.99  
% 3.44/0.99  ------ QBF Options
% 3.44/0.99  
% 3.44/0.99  --qbf_mode                              false
% 3.44/0.99  --qbf_elim_univ                         false
% 3.44/0.99  --qbf_dom_inst                          none
% 3.44/0.99  --qbf_dom_pre_inst                      false
% 3.44/0.99  --qbf_sk_in                             false
% 3.44/0.99  --qbf_pred_elim                         true
% 3.44/0.99  --qbf_split                             512
% 3.44/0.99  
% 3.44/0.99  ------ BMC1 Options
% 3.44/0.99  
% 3.44/0.99  --bmc1_incremental                      false
% 3.44/0.99  --bmc1_axioms                           reachable_all
% 3.44/0.99  --bmc1_min_bound                        0
% 3.44/0.99  --bmc1_max_bound                        -1
% 3.44/0.99  --bmc1_max_bound_default                -1
% 3.44/0.99  --bmc1_symbol_reachability              true
% 3.44/0.99  --bmc1_property_lemmas                  false
% 3.44/0.99  --bmc1_k_induction                      false
% 3.44/0.99  --bmc1_non_equiv_states                 false
% 3.44/0.99  --bmc1_deadlock                         false
% 3.44/0.99  --bmc1_ucm                              false
% 3.44/0.99  --bmc1_add_unsat_core                   none
% 3.44/0.99  --bmc1_unsat_core_children              false
% 3.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/0.99  --bmc1_out_stat                         full
% 3.44/0.99  --bmc1_ground_init                      false
% 3.44/0.99  --bmc1_pre_inst_next_state              false
% 3.44/0.99  --bmc1_pre_inst_state                   false
% 3.44/0.99  --bmc1_pre_inst_reach_state             false
% 3.44/0.99  --bmc1_out_unsat_core                   false
% 3.44/0.99  --bmc1_aig_witness_out                  false
% 3.44/0.99  --bmc1_verbose                          false
% 3.44/0.99  --bmc1_dump_clauses_tptp                false
% 3.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.44/0.99  --bmc1_dump_file                        -
% 3.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.44/0.99  --bmc1_ucm_extend_mode                  1
% 3.44/0.99  --bmc1_ucm_init_mode                    2
% 3.44/0.99  --bmc1_ucm_cone_mode                    none
% 3.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.44/0.99  --bmc1_ucm_relax_model                  4
% 3.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/0.99  --bmc1_ucm_layered_model                none
% 3.44/0.99  --bmc1_ucm_max_lemma_size               10
% 3.44/0.99  
% 3.44/0.99  ------ AIG Options
% 3.44/0.99  
% 3.44/0.99  --aig_mode                              false
% 3.44/0.99  
% 3.44/0.99  ------ Instantiation Options
% 3.44/0.99  
% 3.44/0.99  --instantiation_flag                    true
% 3.44/0.99  --inst_sos_flag                         false
% 3.44/0.99  --inst_sos_phase                        true
% 3.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/0.99  --inst_lit_sel_side                     num_symb
% 3.44/0.99  --inst_solver_per_active                1400
% 3.44/0.99  --inst_solver_calls_frac                1.
% 3.44/0.99  --inst_passive_queue_type               priority_queues
% 3.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/0.99  --inst_passive_queues_freq              [25;2]
% 3.44/0.99  --inst_dismatching                      true
% 3.44/0.99  --inst_eager_unprocessed_to_passive     true
% 3.44/0.99  --inst_prop_sim_given                   true
% 3.44/0.99  --inst_prop_sim_new                     false
% 3.44/0.99  --inst_subs_new                         false
% 3.44/0.99  --inst_eq_res_simp                      false
% 3.44/0.99  --inst_subs_given                       false
% 3.44/0.99  --inst_orphan_elimination               true
% 3.44/0.99  --inst_learning_loop_flag               true
% 3.44/0.99  --inst_learning_start                   3000
% 3.44/0.99  --inst_learning_factor                  2
% 3.44/0.99  --inst_start_prop_sim_after_learn       3
% 3.44/0.99  --inst_sel_renew                        solver
% 3.44/0.99  --inst_lit_activity_flag                true
% 3.44/0.99  --inst_restr_to_given                   false
% 3.44/0.99  --inst_activity_threshold               500
% 3.44/0.99  --inst_out_proof                        true
% 3.44/0.99  
% 3.44/0.99  ------ Resolution Options
% 3.44/0.99  
% 3.44/0.99  --resolution_flag                       true
% 3.44/0.99  --res_lit_sel                           adaptive
% 3.44/0.99  --res_lit_sel_side                      none
% 3.44/0.99  --res_ordering                          kbo
% 3.44/0.99  --res_to_prop_solver                    active
% 3.44/0.99  --res_prop_simpl_new                    false
% 3.44/0.99  --res_prop_simpl_given                  true
% 3.44/0.99  --res_passive_queue_type                priority_queues
% 3.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/0.99  --res_passive_queues_freq               [15;5]
% 3.44/0.99  --res_forward_subs                      full
% 3.44/0.99  --res_backward_subs                     full
% 3.44/0.99  --res_forward_subs_resolution           true
% 3.44/0.99  --res_backward_subs_resolution          true
% 3.44/0.99  --res_orphan_elimination                true
% 3.44/0.99  --res_time_limit                        2.
% 3.44/0.99  --res_out_proof                         true
% 3.44/0.99  
% 3.44/0.99  ------ Superposition Options
% 3.44/0.99  
% 3.44/0.99  --superposition_flag                    true
% 3.44/0.99  --sup_passive_queue_type                priority_queues
% 3.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.44/0.99  --demod_completeness_check              fast
% 3.44/0.99  --demod_use_ground                      true
% 3.44/0.99  --sup_to_prop_solver                    passive
% 3.44/0.99  --sup_prop_simpl_new                    true
% 3.44/0.99  --sup_prop_simpl_given                  true
% 3.44/0.99  --sup_fun_splitting                     false
% 3.44/0.99  --sup_smt_interval                      50000
% 3.44/0.99  
% 3.44/0.99  ------ Superposition Simplification Setup
% 3.44/0.99  
% 3.44/0.99  --sup_indices_passive                   []
% 3.44/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.99  --sup_full_bw                           [BwDemod]
% 3.44/0.99  --sup_immed_triv                        [TrivRules]
% 3.44/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.99  --sup_immed_bw_main                     []
% 3.44/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.99  
% 3.44/0.99  ------ Combination Options
% 3.44/0.99  
% 3.44/0.99  --comb_res_mult                         3
% 3.44/0.99  --comb_sup_mult                         2
% 3.44/0.99  --comb_inst_mult                        10
% 3.44/0.99  
% 3.44/0.99  ------ Debug Options
% 3.44/0.99  
% 3.44/0.99  --dbg_backtrace                         false
% 3.44/0.99  --dbg_dump_prop_clauses                 false
% 3.44/0.99  --dbg_dump_prop_clauses_file            -
% 3.44/0.99  --dbg_out_stat                          false
% 3.44/0.99  ------ Parsing...
% 3.44/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  ------ Proving...
% 3.44/0.99  ------ Problem Properties 
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  clauses                                 31
% 3.44/0.99  conjectures                             10
% 3.44/0.99  EPR                                     6
% 3.44/0.99  Horn                                    29
% 3.44/0.99  unary                                   13
% 3.44/0.99  binary                                  4
% 3.44/0.99  lits                                    89
% 3.44/0.99  lits eq                                 16
% 3.44/0.99  fd_pure                                 0
% 3.44/0.99  fd_pseudo                               0
% 3.44/0.99  fd_cond                                 1
% 3.44/0.99  fd_pseudo_cond                          4
% 3.44/0.99  AC symbols                              0
% 3.44/0.99  
% 3.44/0.99  ------ Schedule dynamic 5 is on 
% 3.44/0.99  
% 3.44/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ 
% 3.44/0.99  Current options:
% 3.44/0.99  ------ 
% 3.44/0.99  
% 3.44/0.99  ------ Input Options
% 3.44/0.99  
% 3.44/0.99  --out_options                           all
% 3.44/0.99  --tptp_safe_out                         true
% 3.44/0.99  --problem_path                          ""
% 3.44/0.99  --include_path                          ""
% 3.44/0.99  --clausifier                            res/vclausify_rel
% 3.44/0.99  --clausifier_options                    --mode clausify
% 3.44/0.99  --stdin                                 false
% 3.44/0.99  --stats_out                             all
% 3.44/0.99  
% 3.44/0.99  ------ General Options
% 3.44/0.99  
% 3.44/0.99  --fof                                   false
% 3.44/0.99  --time_out_real                         305.
% 3.44/0.99  --time_out_virtual                      -1.
% 3.44/0.99  --symbol_type_check                     false
% 3.44/0.99  --clausify_out                          false
% 3.44/0.99  --sig_cnt_out                           false
% 3.44/0.99  --trig_cnt_out                          false
% 3.44/0.99  --trig_cnt_out_tolerance                1.
% 3.44/0.99  --trig_cnt_out_sk_spl                   false
% 3.44/0.99  --abstr_cl_out                          false
% 3.44/0.99  
% 3.44/0.99  ------ Global Options
% 3.44/0.99  
% 3.44/0.99  --schedule                              default
% 3.44/0.99  --add_important_lit                     false
% 3.44/0.99  --prop_solver_per_cl                    1000
% 3.44/0.99  --min_unsat_core                        false
% 3.44/0.99  --soft_assumptions                      false
% 3.44/0.99  --soft_lemma_size                       3
% 3.44/0.99  --prop_impl_unit_size                   0
% 3.44/0.99  --prop_impl_unit                        []
% 3.44/0.99  --share_sel_clauses                     true
% 3.44/0.99  --reset_solvers                         false
% 3.44/0.99  --bc_imp_inh                            [conj_cone]
% 3.44/0.99  --conj_cone_tolerance                   3.
% 3.44/0.99  --extra_neg_conj                        none
% 3.44/0.99  --large_theory_mode                     true
% 3.44/0.99  --prolific_symb_bound                   200
% 3.44/0.99  --lt_threshold                          2000
% 3.44/0.99  --clause_weak_htbl                      true
% 3.44/0.99  --gc_record_bc_elim                     false
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing Options
% 3.44/0.99  
% 3.44/0.99  --preprocessing_flag                    true
% 3.44/0.99  --time_out_prep_mult                    0.1
% 3.44/0.99  --splitting_mode                        input
% 3.44/0.99  --splitting_grd                         true
% 3.44/0.99  --splitting_cvd                         false
% 3.44/0.99  --splitting_cvd_svl                     false
% 3.44/0.99  --splitting_nvd                         32
% 3.44/0.99  --sub_typing                            true
% 3.44/0.99  --prep_gs_sim                           true
% 3.44/0.99  --prep_unflatten                        true
% 3.44/0.99  --prep_res_sim                          true
% 3.44/0.99  --prep_upred                            true
% 3.44/0.99  --prep_sem_filter                       exhaustive
% 3.44/0.99  --prep_sem_filter_out                   false
% 3.44/0.99  --pred_elim                             true
% 3.44/0.99  --res_sim_input                         true
% 3.44/0.99  --eq_ax_congr_red                       true
% 3.44/0.99  --pure_diseq_elim                       true
% 3.44/0.99  --brand_transform                       false
% 3.44/0.99  --non_eq_to_eq                          false
% 3.44/0.99  --prep_def_merge                        true
% 3.44/0.99  --prep_def_merge_prop_impl              false
% 3.44/0.99  --prep_def_merge_mbd                    true
% 3.44/0.99  --prep_def_merge_tr_red                 false
% 3.44/0.99  --prep_def_merge_tr_cl                  false
% 3.44/0.99  --smt_preprocessing                     true
% 3.44/0.99  --smt_ac_axioms                         fast
% 3.44/0.99  --preprocessed_out                      false
% 3.44/0.99  --preprocessed_stats                    false
% 3.44/0.99  
% 3.44/0.99  ------ Abstraction refinement Options
% 3.44/0.99  
% 3.44/0.99  --abstr_ref                             []
% 3.44/0.99  --abstr_ref_prep                        false
% 3.44/0.99  --abstr_ref_until_sat                   false
% 3.44/0.99  --abstr_ref_sig_restrict                funpre
% 3.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/0.99  --abstr_ref_under                       []
% 3.44/0.99  
% 3.44/0.99  ------ SAT Options
% 3.44/0.99  
% 3.44/0.99  --sat_mode                              false
% 3.44/0.99  --sat_fm_restart_options                ""
% 3.44/0.99  --sat_gr_def                            false
% 3.44/0.99  --sat_epr_types                         true
% 3.44/0.99  --sat_non_cyclic_types                  false
% 3.44/0.99  --sat_finite_models                     false
% 3.44/0.99  --sat_fm_lemmas                         false
% 3.44/0.99  --sat_fm_prep                           false
% 3.44/0.99  --sat_fm_uc_incr                        true
% 3.44/0.99  --sat_out_model                         small
% 3.44/0.99  --sat_out_clauses                       false
% 3.44/0.99  
% 3.44/0.99  ------ QBF Options
% 3.44/0.99  
% 3.44/0.99  --qbf_mode                              false
% 3.44/0.99  --qbf_elim_univ                         false
% 3.44/0.99  --qbf_dom_inst                          none
% 3.44/0.99  --qbf_dom_pre_inst                      false
% 3.44/0.99  --qbf_sk_in                             false
% 3.44/0.99  --qbf_pred_elim                         true
% 3.44/0.99  --qbf_split                             512
% 3.44/0.99  
% 3.44/0.99  ------ BMC1 Options
% 3.44/0.99  
% 3.44/0.99  --bmc1_incremental                      false
% 3.44/0.99  --bmc1_axioms                           reachable_all
% 3.44/0.99  --bmc1_min_bound                        0
% 3.44/0.99  --bmc1_max_bound                        -1
% 3.44/0.99  --bmc1_max_bound_default                -1
% 3.44/0.99  --bmc1_symbol_reachability              true
% 3.44/0.99  --bmc1_property_lemmas                  false
% 3.44/0.99  --bmc1_k_induction                      false
% 3.44/0.99  --bmc1_non_equiv_states                 false
% 3.44/0.99  --bmc1_deadlock                         false
% 3.44/0.99  --bmc1_ucm                              false
% 3.44/0.99  --bmc1_add_unsat_core                   none
% 3.44/0.99  --bmc1_unsat_core_children              false
% 3.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/0.99  --bmc1_out_stat                         full
% 3.44/0.99  --bmc1_ground_init                      false
% 3.44/0.99  --bmc1_pre_inst_next_state              false
% 3.44/0.99  --bmc1_pre_inst_state                   false
% 3.44/0.99  --bmc1_pre_inst_reach_state             false
% 3.44/0.99  --bmc1_out_unsat_core                   false
% 3.44/0.99  --bmc1_aig_witness_out                  false
% 3.44/0.99  --bmc1_verbose                          false
% 3.44/0.99  --bmc1_dump_clauses_tptp                false
% 3.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.44/0.99  --bmc1_dump_file                        -
% 3.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.44/0.99  --bmc1_ucm_extend_mode                  1
% 3.44/0.99  --bmc1_ucm_init_mode                    2
% 3.44/0.99  --bmc1_ucm_cone_mode                    none
% 3.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.44/0.99  --bmc1_ucm_relax_model                  4
% 3.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/0.99  --bmc1_ucm_layered_model                none
% 3.44/0.99  --bmc1_ucm_max_lemma_size               10
% 3.44/0.99  
% 3.44/0.99  ------ AIG Options
% 3.44/0.99  
% 3.44/0.99  --aig_mode                              false
% 3.44/0.99  
% 3.44/0.99  ------ Instantiation Options
% 3.44/0.99  
% 3.44/0.99  --instantiation_flag                    true
% 3.44/0.99  --inst_sos_flag                         false
% 3.44/0.99  --inst_sos_phase                        true
% 3.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/0.99  --inst_lit_sel_side                     none
% 3.44/0.99  --inst_solver_per_active                1400
% 3.44/0.99  --inst_solver_calls_frac                1.
% 3.44/0.99  --inst_passive_queue_type               priority_queues
% 3.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/0.99  --inst_passive_queues_freq              [25;2]
% 3.44/0.99  --inst_dismatching                      true
% 3.44/0.99  --inst_eager_unprocessed_to_passive     true
% 3.44/0.99  --inst_prop_sim_given                   true
% 3.44/0.99  --inst_prop_sim_new                     false
% 3.44/0.99  --inst_subs_new                         false
% 3.44/0.99  --inst_eq_res_simp                      false
% 3.44/0.99  --inst_subs_given                       false
% 3.44/0.99  --inst_orphan_elimination               true
% 3.44/0.99  --inst_learning_loop_flag               true
% 3.44/0.99  --inst_learning_start                   3000
% 3.44/0.99  --inst_learning_factor                  2
% 3.44/0.99  --inst_start_prop_sim_after_learn       3
% 3.44/0.99  --inst_sel_renew                        solver
% 3.44/0.99  --inst_lit_activity_flag                true
% 3.44/0.99  --inst_restr_to_given                   false
% 3.44/0.99  --inst_activity_threshold               500
% 3.44/0.99  --inst_out_proof                        true
% 3.44/0.99  
% 3.44/0.99  ------ Resolution Options
% 3.44/0.99  
% 3.44/0.99  --resolution_flag                       false
% 3.44/0.99  --res_lit_sel                           adaptive
% 3.44/0.99  --res_lit_sel_side                      none
% 3.44/0.99  --res_ordering                          kbo
% 3.44/0.99  --res_to_prop_solver                    active
% 3.44/0.99  --res_prop_simpl_new                    false
% 3.44/0.99  --res_prop_simpl_given                  true
% 3.44/0.99  --res_passive_queue_type                priority_queues
% 3.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/0.99  --res_passive_queues_freq               [15;5]
% 3.44/0.99  --res_forward_subs                      full
% 3.44/0.99  --res_backward_subs                     full
% 3.44/0.99  --res_forward_subs_resolution           true
% 3.44/0.99  --res_backward_subs_resolution          true
% 3.44/0.99  --res_orphan_elimination                true
% 3.44/0.99  --res_time_limit                        2.
% 3.44/0.99  --res_out_proof                         true
% 3.44/0.99  
% 3.44/0.99  ------ Superposition Options
% 3.44/0.99  
% 3.44/0.99  --superposition_flag                    true
% 3.44/0.99  --sup_passive_queue_type                priority_queues
% 3.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.44/0.99  --demod_completeness_check              fast
% 3.44/0.99  --demod_use_ground                      true
% 3.44/0.99  --sup_to_prop_solver                    passive
% 3.44/0.99  --sup_prop_simpl_new                    true
% 3.44/0.99  --sup_prop_simpl_given                  true
% 3.44/0.99  --sup_fun_splitting                     false
% 3.44/0.99  --sup_smt_interval                      50000
% 3.44/0.99  
% 3.44/0.99  ------ Superposition Simplification Setup
% 3.44/0.99  
% 3.44/0.99  --sup_indices_passive                   []
% 3.44/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.99  --sup_full_bw                           [BwDemod]
% 3.44/0.99  --sup_immed_triv                        [TrivRules]
% 3.44/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.99  --sup_immed_bw_main                     []
% 3.44/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.99  
% 3.44/0.99  ------ Combination Options
% 3.44/0.99  
% 3.44/0.99  --comb_res_mult                         3
% 3.44/0.99  --comb_sup_mult                         2
% 3.44/0.99  --comb_inst_mult                        10
% 3.44/0.99  
% 3.44/0.99  ------ Debug Options
% 3.44/0.99  
% 3.44/0.99  --dbg_backtrace                         false
% 3.44/0.99  --dbg_dump_prop_clauses                 false
% 3.44/0.99  --dbg_dump_prop_clauses_file            -
% 3.44/0.99  --dbg_out_stat                          false
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  % SZS status Theorem for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  fof(f15,conjecture,(
% 3.44/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f16,negated_conjecture,(
% 3.44/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.44/0.99    inference(negated_conjecture,[],[f15])).
% 3.44/0.99  
% 3.44/0.99  fof(f38,plain,(
% 3.44/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.44/0.99    inference(ennf_transformation,[],[f16])).
% 3.44/0.99  
% 3.44/0.99  fof(f39,plain,(
% 3.44/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.44/0.99    inference(flattening,[],[f38])).
% 3.44/0.99  
% 3.44/0.99  fof(f45,plain,(
% 3.44/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f44,plain,(
% 3.44/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f46,plain,(
% 3.44/0.99    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f45,f44])).
% 3.44/0.99  
% 3.44/0.99  fof(f79,plain,(
% 3.44/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f74,plain,(
% 3.44/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f7,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f23,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(ennf_transformation,[],[f7])).
% 3.44/0.99  
% 3.44/0.99  fof(f55,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f23])).
% 3.44/0.99  
% 3.44/0.99  fof(f6,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f17,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.44/0.99    inference(pure_predicate_removal,[],[f6])).
% 3.44/0.99  
% 3.44/0.99  fof(f22,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(ennf_transformation,[],[f17])).
% 3.44/0.99  
% 3.44/0.99  fof(f54,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f22])).
% 3.44/0.99  
% 3.44/0.99  fof(f11,axiom,(
% 3.44/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f30,plain,(
% 3.44/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.44/0.99    inference(ennf_transformation,[],[f11])).
% 3.44/0.99  
% 3.44/0.99  fof(f31,plain,(
% 3.44/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.44/0.99    inference(flattening,[],[f30])).
% 3.44/0.99  
% 3.44/0.99  fof(f43,plain,(
% 3.44/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.44/0.99    inference(nnf_transformation,[],[f31])).
% 3.44/0.99  
% 3.44/0.99  fof(f63,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f43])).
% 3.44/0.99  
% 3.44/0.99  fof(f5,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f21,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(ennf_transformation,[],[f5])).
% 3.44/0.99  
% 3.44/0.99  fof(f53,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f21])).
% 3.44/0.99  
% 3.44/0.99  fof(f71,plain,(
% 3.44/0.99    v1_funct_1(sK1)),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f73,plain,(
% 3.44/0.99    v3_funct_2(sK1,sK0,sK0)),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f9,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f26,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(ennf_transformation,[],[f9])).
% 3.44/0.99  
% 3.44/0.99  fof(f27,plain,(
% 3.44/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(flattening,[],[f26])).
% 3.44/0.99  
% 3.44/0.99  fof(f60,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f27])).
% 3.44/0.99  
% 3.44/0.99  fof(f14,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f36,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.44/0.99    inference(ennf_transformation,[],[f14])).
% 3.44/0.99  
% 3.44/0.99  fof(f37,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.44/0.99    inference(flattening,[],[f36])).
% 3.44/0.99  
% 3.44/0.99  fof(f70,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f37])).
% 3.44/0.99  
% 3.44/0.99  fof(f72,plain,(
% 3.44/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f59,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f27])).
% 3.44/0.99  
% 3.44/0.99  fof(f75,plain,(
% 3.44/0.99    v1_funct_1(sK2)),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f76,plain,(
% 3.44/0.99    v1_funct_2(sK2,sK0,sK0)),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f78,plain,(
% 3.44/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f13,axiom,(
% 3.44/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f34,plain,(
% 3.44/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.44/0.99    inference(ennf_transformation,[],[f13])).
% 3.44/0.99  
% 3.44/0.99  fof(f35,plain,(
% 3.44/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.44/0.99    inference(flattening,[],[f34])).
% 3.44/0.99  
% 3.44/0.99  fof(f69,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f35])).
% 3.44/0.99  
% 3.44/0.99  fof(f80,plain,(
% 3.44/0.99    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f8,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f24,plain,(
% 3.44/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.44/0.99    inference(ennf_transformation,[],[f8])).
% 3.44/0.99  
% 3.44/0.99  fof(f25,plain,(
% 3.44/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(flattening,[],[f24])).
% 3.44/0.99  
% 3.44/0.99  fof(f42,plain,(
% 3.44/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(nnf_transformation,[],[f25])).
% 3.44/0.99  
% 3.44/0.99  fof(f57,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f42])).
% 3.44/0.99  
% 3.44/0.99  fof(f83,plain,(
% 3.44/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(equality_resolution,[],[f57])).
% 3.44/0.99  
% 3.44/0.99  fof(f77,plain,(
% 3.44/0.99    v3_funct_2(sK2,sK0,sK0)),
% 3.44/0.99    inference(cnf_transformation,[],[f46])).
% 3.44/0.99  
% 3.44/0.99  fof(f1,axiom,(
% 3.44/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f40,plain,(
% 3.44/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.44/0.99    inference(nnf_transformation,[],[f1])).
% 3.44/0.99  
% 3.44/0.99  fof(f41,plain,(
% 3.44/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.44/0.99    inference(flattening,[],[f40])).
% 3.44/0.99  
% 3.44/0.99  fof(f49,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.44/0.99    inference(cnf_transformation,[],[f41])).
% 3.44/0.99  
% 3.44/0.99  fof(f81,plain,(
% 3.44/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.44/0.99    inference(equality_resolution,[],[f49])).
% 3.44/0.99  
% 3.44/0.99  fof(f12,axiom,(
% 3.44/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f32,plain,(
% 3.44/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.44/0.99    inference(ennf_transformation,[],[f12])).
% 3.44/0.99  
% 3.44/0.99  fof(f33,plain,(
% 3.44/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.44/0.99    inference(flattening,[],[f32])).
% 3.44/0.99  
% 3.44/0.99  fof(f68,plain,(
% 3.44/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f33])).
% 3.44/0.99  
% 3.44/0.99  fof(f65,plain,(
% 3.44/0.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f33])).
% 3.44/0.99  
% 3.44/0.99  fof(f67,plain,(
% 3.44/0.99    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f33])).
% 3.44/0.99  
% 3.44/0.99  fof(f48,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.44/0.99    inference(cnf_transformation,[],[f41])).
% 3.44/0.99  
% 3.44/0.99  fof(f82,plain,(
% 3.44/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.44/0.99    inference(equality_resolution,[],[f48])).
% 3.44/0.99  
% 3.44/0.99  fof(f4,axiom,(
% 3.44/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f19,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.44/0.99    inference(ennf_transformation,[],[f4])).
% 3.44/0.99  
% 3.44/0.99  fof(f20,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : (X0 = X1 | k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.44/0.99    inference(flattening,[],[f19])).
% 3.44/0.99  
% 3.44/0.99  fof(f52,plain,(
% 3.44/0.99    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f20])).
% 3.44/0.99  
% 3.44/0.99  cnf(c_25,negated_conjecture,
% 3.44/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.44/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1653,plain,
% 3.44/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_30,negated_conjecture,
% 3.44/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1648,plain,
% 3.44/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1666,plain,
% 3.44/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.44/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3449,plain,
% 3.44/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1648,c_1666]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7,plain,
% 3.44/0.99      ( v5_relat_1(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_17,plain,
% 3.44/0.99      ( ~ v2_funct_2(X0,X1)
% 3.44/0.99      | ~ v5_relat_1(X0,X1)
% 3.44/0.99      | ~ v1_relat_1(X0)
% 3.44/0.99      | k2_relat_1(X0) = X1 ),
% 3.44/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_331,plain,
% 3.44/0.99      ( ~ v2_funct_2(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.44/0.99      | ~ v1_relat_1(X0)
% 3.44/0.99      | k2_relat_1(X0) = X1 ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_7,c_17]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_6,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | v1_relat_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_343,plain,
% 3.44/0.99      ( ~ v2_funct_2(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.44/0.99      | k2_relat_1(X0) = X1 ),
% 3.44/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_331,c_6]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1644,plain,
% 3.44/0.99      ( k2_relat_1(X0) = X1
% 3.44/0.99      | v2_funct_2(X0,X1) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2701,plain,
% 3.44/0.99      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1648,c_1644]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_33,negated_conjecture,
% 3.44/0.99      ( v1_funct_1(sK1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_31,negated_conjecture,
% 3.44/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_11,plain,
% 3.44/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.44/0.99      | v2_funct_2(X0,X2)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | ~ v1_funct_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1983,plain,
% 3.44/0.99      ( ~ v3_funct_2(sK1,X0,X1)
% 3.44/0.99      | v2_funct_2(sK1,X1)
% 3.44/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.44/0.99      | ~ v1_funct_1(sK1) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1985,plain,
% 3.44/0.99      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.44/0.99      | v2_funct_2(sK1,sK0)
% 3.44/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | ~ v1_funct_1(sK1) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1983]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2221,plain,
% 3.44/0.99      ( ~ v2_funct_2(sK1,X0)
% 3.44/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.44/0.99      | k2_relat_1(sK1) = X0 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_343]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2223,plain,
% 3.44/0.99      ( ~ v2_funct_2(sK1,sK0)
% 3.44/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | k2_relat_1(sK1) = sK0 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_2221]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3324,plain,
% 3.44/0.99      ( k2_relat_1(sK1) = sK0 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_2701,c_33,c_31,c_30,c_1985,c_2223]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3461,plain,
% 3.44/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.44/0.99      inference(light_normalisation,[status(thm)],[c_3449,c_3324]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_23,plain,
% 3.44/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.44/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.44/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.44/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.44/0.99      | ~ v2_funct_1(X2)
% 3.44/0.99      | ~ v1_funct_1(X2)
% 3.44/0.99      | ~ v1_funct_1(X3)
% 3.44/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.44/0.99      | k2_funct_1(X2) = X3
% 3.44/0.99      | k1_xboole_0 = X1
% 3.44/0.99      | k1_xboole_0 = X0 ),
% 3.44/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1655,plain,
% 3.44/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.44/0.99      | k2_funct_1(X2) = X3
% 3.44/0.99      | k1_xboole_0 = X1
% 3.44/0.99      | k1_xboole_0 = X0
% 3.44/0.99      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.44/0.99      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.44/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.44/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.44/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.44/0.99      | v2_funct_1(X2) != iProver_top
% 3.44/0.99      | v1_funct_1(X2) != iProver_top
% 3.44/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3551,plain,
% 3.44/0.99      ( k2_funct_1(sK1) = X0
% 3.44/0.99      | sK0 = k1_xboole_0
% 3.44/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.44/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.44/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | v2_funct_1(sK1) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top
% 3.44/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3461,c_1655]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_34,plain,
% 3.44/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_32,negated_conjecture,
% 3.44/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_35,plain,
% 3.44/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_36,plain,
% 3.44/0.99      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_37,plain,
% 3.44/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12,plain,
% 3.44/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | v2_funct_1(X0)
% 3.44/0.99      | ~ v1_funct_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1958,plain,
% 3.44/0.99      ( ~ v3_funct_2(sK1,X0,X1)
% 3.44/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.44/0.99      | v2_funct_1(sK1)
% 3.44/0.99      | ~ v1_funct_1(sK1) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1959,plain,
% 3.44/0.99      ( v3_funct_2(sK1,X0,X1) != iProver_top
% 3.44/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.44/0.99      | v2_funct_1(sK1) = iProver_top
% 3.44/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1958]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1961,plain,
% 3.44/0.99      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.44/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | v2_funct_1(sK1) = iProver_top
% 3.44/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1959]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4130,plain,
% 3.44/0.99      ( v1_funct_1(X0) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | k2_funct_1(sK1) = X0
% 3.44/0.99      | sK0 = k1_xboole_0
% 3.44/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.44/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_3551,c_34,c_35,c_36,c_37,c_1961]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4131,plain,
% 3.44/0.99      ( k2_funct_1(sK1) = X0
% 3.44/0.99      | sK0 = k1_xboole_0
% 3.44/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.44/0.99      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_4130]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4142,plain,
% 3.44/0.99      ( k2_funct_1(sK1) = sK2
% 3.44/0.99      | sK0 = k1_xboole_0
% 3.44/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1653,c_4131]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_29,negated_conjecture,
% 3.44/0.99      ( v1_funct_1(sK2) ),
% 3.44/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_28,negated_conjecture,
% 3.44/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_26,negated_conjecture,
% 3.44/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4143,plain,
% 3.44/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | ~ v1_funct_1(sK2)
% 3.44/0.99      | k2_funct_1(sK1) = sK2
% 3.44/0.99      | sK0 = k1_xboole_0 ),
% 3.44/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4142]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4268,plain,
% 3.44/0.99      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_4142,c_38,c_39,c_41]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4269,plain,
% 3.44/0.99      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_4268]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_22,plain,
% 3.44/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.44/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.44/0.99      | ~ v1_funct_1(X0)
% 3.44/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1656,plain,
% 3.44/0.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.44/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.44/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.44/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.44/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7383,plain,
% 3.44/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.44/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.44/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.44/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1648,c_1656]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2032,plain,
% 3.44/0.99      ( ~ v1_funct_2(sK1,X0,X0)
% 3.44/0.99      | ~ v3_funct_2(sK1,X0,X0)
% 3.44/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.44/0.99      | ~ v1_funct_1(sK1)
% 3.44/0.99      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2034,plain,
% 3.44/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.44/0.99      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.44/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | ~ v1_funct_1(sK1)
% 3.44/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_2032]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7621,plain,
% 3.44/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_7383,c_33,c_32,c_31,c_30,c_2034]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_24,negated_conjecture,
% 3.44/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.44/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1654,plain,
% 3.44/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7626,plain,
% 3.44/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_7621,c_1654]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7768,plain,
% 3.44/0.99      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4269,c_7626]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_41,plain,
% 3.44/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1124,plain,( X0 = X0 ),theory(equality) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1151,plain,
% 3.44/0.99      ( sK0 = sK0 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1124]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9,plain,
% 3.44/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1947,plain,
% 3.44/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1948,plain,
% 3.44/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.44/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1947]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2186,plain,
% 3.44/0.99      ( sK2 = sK2 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1124]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1130,plain,
% 3.44/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.44/0.99      | r2_relset_1(X4,X5,X6,X7)
% 3.44/0.99      | X4 != X0
% 3.44/0.99      | X5 != X1
% 3.44/0.99      | X6 != X2
% 3.44/0.99      | X7 != X3 ),
% 3.44/0.99      theory(equality) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2105,plain,
% 3.44/0.99      ( r2_relset_1(X0,X1,X2,X3)
% 3.44/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 3.44/0.99      | X2 != sK2
% 3.44/0.99      | X3 != sK2
% 3.44/0.99      | X0 != sK0
% 3.44/0.99      | X1 != sK0 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1130]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2607,plain,
% 3.44/0.99      ( r2_relset_1(X0,X1,sK2,X2)
% 3.44/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 3.44/0.99      | X2 != sK2
% 3.44/0.99      | X0 != sK0
% 3.44/0.99      | X1 != sK0
% 3.44/0.99      | sK2 != sK2 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_2105]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7281,plain,
% 3.44/0.99      ( r2_relset_1(X0,X1,sK2,k2_funct_1(sK1))
% 3.44/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 3.44/0.99      | X0 != sK0
% 3.44/0.99      | X1 != sK0
% 3.44/0.99      | k2_funct_1(sK1) != sK2
% 3.44/0.99      | sK2 != sK2 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_2607]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7287,plain,
% 3.44/0.99      ( X0 != sK0
% 3.44/0.99      | X1 != sK0
% 3.44/0.99      | k2_funct_1(sK1) != sK2
% 3.44/0.99      | sK2 != sK2
% 3.44/0.99      | r2_relset_1(X0,X1,sK2,k2_funct_1(sK1)) = iProver_top
% 3.44/0.99      | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_7281]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7289,plain,
% 3.44/0.99      ( k2_funct_1(sK1) != sK2
% 3.44/0.99      | sK2 != sK2
% 3.44/0.99      | sK0 != sK0
% 3.44/0.99      | r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) = iProver_top
% 3.44/0.99      | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_7287]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8737,plain,
% 3.44/0.99      ( sK0 = k1_xboole_0 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_7768,c_41,c_1151,c_1948,c_2186,c_4269,c_7289,c_7626]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1652,plain,
% 3.44/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7382,plain,
% 3.44/0.99      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 3.44/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1652,c_1656]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_27,negated_conjecture,
% 3.44/0.99      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2027,plain,
% 3.44/0.99      ( ~ v1_funct_2(sK2,X0,X0)
% 3.44/0.99      | ~ v3_funct_2(sK2,X0,X0)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.44/0.99      | ~ v1_funct_1(sK2)
% 3.44/0.99      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2029,plain,
% 3.44/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.44/0.99      | ~ v3_funct_2(sK2,sK0,sK0)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | ~ v1_funct_1(sK2)
% 3.44/0.99      | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_2027]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7609,plain,
% 3.44/0.99      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_7382,c_29,c_28,c_27,c_26,c_2029]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8746,plain,
% 3.44/0.99      ( k2_funct_2(k1_xboole_0,sK2) = k2_funct_1(sK2) ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8737,c_7609]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_0,plain,
% 3.44/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.44/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_18,plain,
% 3.44/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.44/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.44/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.44/0.99      | ~ v1_funct_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1660,plain,
% 3.44/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.44/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1663,plain,
% 3.44/0.99      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.44/0.99      | v2_funct_2(X0,X2) = iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7977,plain,
% 3.44/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) != iProver_top
% 3.44/0.99      | v2_funct_2(k2_funct_2(X1,X0),X1) = iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top
% 3.44/0.99      | v1_funct_1(k2_funct_2(X1,X0)) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1660,c_1663]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_21,plain,
% 3.44/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.44/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.44/0.99      | ~ v1_funct_1(X0)
% 3.44/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.44/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_50,plain,
% 3.44/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top
% 3.44/0.99      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_19,plain,
% 3.44/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.44/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.44/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.44/0.99      | ~ v1_funct_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_56,plain,
% 3.44/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_10681,plain,
% 3.44/0.99      ( v1_funct_1(X0) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.44/0.99      | v2_funct_2(k2_funct_2(X1,X0),X1) = iProver_top
% 3.44/0.99      | v1_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,X1,X1) != iProver_top ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_7977,c_50,c_56]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_10682,plain,
% 3.44/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v2_funct_2(k2_funct_2(X1,X0),X1) = iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_10681]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_10693,plain,
% 3.44/0.99      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.44/0.99      | v2_funct_2(k2_funct_2(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_0,c_10682]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_10733,plain,
% 3.44/0.99      ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.44/0.99      | v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.44/0.99      | v2_funct_2(k2_funct_1(sK2),k1_xboole_0) = iProver_top
% 3.44/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.44/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_8746,c_10693]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_38,plain,
% 3.44/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1651,plain,
% 3.44/0.99      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8767,plain,
% 3.44/0.99      ( v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8737,c_1651]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1650,plain,
% 3.44/0.99      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8768,plain,
% 3.44/0.99      ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8737,c_1650]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8765,plain,
% 3.44/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8737,c_1652]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1,plain,
% 3.44/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.44/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8783,plain,
% 3.44/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8765,c_1]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_11178,plain,
% 3.44/0.99      ( v2_funct_2(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_10733,c_38,c_8767,c_8768,c_8783]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7970,plain,
% 3.44/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.44/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_7609,c_1660]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_39,plain,
% 3.44/0.99      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_40,plain,
% 3.44/0.99      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9657,plain,
% 3.44/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_7970,c_38,c_39,c_40,c_41]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9661,plain,
% 3.44/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.44/0.99      inference(light_normalisation,[status(thm)],[c_9657,c_8737]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9662,plain,
% 3.44/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_9661,c_1]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2703,plain,
% 3.44/0.99      ( k2_relat_1(X0) = X1
% 3.44/0.99      | v2_funct_2(X0,X1) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1,c_1644]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9674,plain,
% 3.44/0.99      ( k2_relat_1(k2_funct_1(sK2)) = X0
% 3.44/0.99      | v2_funct_2(k2_funct_1(sK2),X0) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_9662,c_2703]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_11430,plain,
% 3.44/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_11178,c_9674]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2700,plain,
% 3.44/0.99      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1652,c_1644]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1978,plain,
% 3.44/0.99      ( ~ v3_funct_2(sK2,X0,X1)
% 3.44/0.99      | v2_funct_2(sK2,X1)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.44/0.99      | ~ v1_funct_1(sK2) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1980,plain,
% 3.44/0.99      ( ~ v3_funct_2(sK2,sK0,sK0)
% 3.44/0.99      | v2_funct_2(sK2,sK0)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | ~ v1_funct_1(sK2) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1978]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2202,plain,
% 3.44/0.99      ( ~ v2_funct_2(sK2,X0)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.44/0.99      | k2_relat_1(sK2) = X0 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_343]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2204,plain,
% 3.44/0.99      ( ~ v2_funct_2(sK2,sK0)
% 3.44/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | k2_relat_1(sK2) = sK0 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_2202]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3154,plain,
% 3.44/0.99      ( k2_relat_1(sK2) = sK0 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_2700,c_29,c_27,c_26,c_1980,c_2204]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_5,plain,
% 3.44/0.99      ( ~ v1_relat_1(X0)
% 3.44/0.99      | ~ v1_relat_1(X1)
% 3.44/0.99      | X1 = X0
% 3.44/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.44/0.99      | k2_relat_1(X1) != k1_xboole_0 ),
% 3.44/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1668,plain,
% 3.44/0.99      ( X0 = X1
% 3.44/0.99      | k2_relat_1(X1) != k1_xboole_0
% 3.44/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.44/0.99      | v1_relat_1(X1) != iProver_top
% 3.44/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4334,plain,
% 3.44/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.44/0.99      | sK2 = X0
% 3.44/0.99      | sK0 != k1_xboole_0
% 3.44/0.99      | v1_relat_1(X0) != iProver_top
% 3.44/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3154,c_1668]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1921,plain,
% 3.44/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | v1_relat_1(sK2) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1922,plain,
% 3.44/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1921]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4363,plain,
% 3.44/0.99      ( v1_relat_1(X0) != iProver_top
% 3.44/0.99      | sK0 != k1_xboole_0
% 3.44/0.99      | sK2 = X0
% 3.44/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_4334,c_41,c_1922]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4364,plain,
% 3.44/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.44/0.99      | sK2 = X0
% 3.44/0.99      | sK0 != k1_xboole_0
% 3.44/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_4363]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8753,plain,
% 3.44/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.44/0.99      | sK2 = X0
% 3.44/0.99      | k1_xboole_0 != k1_xboole_0
% 3.44/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8737,c_4364]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8803,plain,
% 3.44/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.44/0.99      | sK2 = X0
% 3.44/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.99      inference(equality_resolution_simp,[status(thm)],[c_8753]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_11615,plain,
% 3.44/0.99      ( k2_funct_1(sK2) = sK2
% 3.44/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_11430,c_8803]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1667,plain,
% 3.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7979,plain,
% 3.44/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.44/0.99      | v1_funct_1(X0) != iProver_top
% 3.44/0.99      | v1_relat_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1660,c_1667]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8560,plain,
% 3.44/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | v1_funct_1(sK2) != iProver_top
% 3.44/0.99      | v1_relat_1(k2_funct_2(sK0,sK2)) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_1652,c_7979]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8577,plain,
% 3.44/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.44/0.99      | v1_funct_1(sK2) != iProver_top
% 3.44/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.44/0.99      inference(light_normalisation,[status(thm)],[c_8560,c_7609]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12960,plain,
% 3.44/0.99      ( k2_funct_1(sK2) = sK2 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_11615,c_38,c_39,c_40,c_8577]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8744,plain,
% 3.44/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8737,c_7626]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4374,plain,
% 3.44/0.99      ( sK1 = sK2 | sK0 != k1_xboole_0 | v1_relat_1(sK1) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3324,c_4364]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1924,plain,
% 3.44/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.44/0.99      | v1_relat_1(sK1) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1925,plain,
% 3.44/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.44/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4425,plain,
% 3.44/0.99      ( sK0 != k1_xboole_0 | sK1 = sK2 ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_4374,c_37,c_1925]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4426,plain,
% 3.44/0.99      ( sK1 = sK2 | sK0 != k1_xboole_0 ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_4425]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8752,plain,
% 3.44/0.99      ( sK1 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_8737,c_4426]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8810,plain,
% 3.44/0.99      ( sK1 = sK2 ),
% 3.44/0.99      inference(equality_resolution_simp,[status(thm)],[c_8752]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8837,plain,
% 3.44/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) != iProver_top ),
% 3.44/0.99      inference(light_normalisation,[status(thm)],[c_8744,c_8810]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12984,plain,
% 3.44/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) != iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_12960,c_8837]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1665,plain,
% 3.44/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.44/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2997,plain,
% 3.44/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1652,c_1665]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_8763,plain,
% 3.44/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_8737,c_2997]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(contradiction,plain,
% 3.44/1.00      ( $false ),
% 3.44/1.00      inference(minisat,[status(thm)],[c_12984,c_8763]) ).
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  ------                               Statistics
% 3.44/1.00  
% 3.44/1.00  ------ General
% 3.44/1.00  
% 3.44/1.00  abstr_ref_over_cycles:                  0
% 3.44/1.00  abstr_ref_under_cycles:                 0
% 3.44/1.00  gc_basic_clause_elim:                   0
% 3.44/1.00  forced_gc_time:                         0
% 3.44/1.00  parsing_time:                           0.01
% 3.44/1.00  unif_index_cands_time:                  0.
% 3.44/1.00  unif_index_add_time:                    0.
% 3.44/1.00  orderings_time:                         0.
% 3.44/1.00  out_proof_time:                         0.013
% 3.44/1.00  total_time:                             0.43
% 3.44/1.00  num_of_symbols:                         52
% 3.44/1.00  num_of_terms:                           13373
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing
% 3.44/1.00  
% 3.44/1.00  num_of_splits:                          0
% 3.44/1.00  num_of_split_atoms:                     0
% 3.44/1.00  num_of_reused_defs:                     0
% 3.44/1.00  num_eq_ax_congr_red:                    22
% 3.44/1.00  num_of_sem_filtered_clauses:            1
% 3.44/1.00  num_of_subtypes:                        0
% 3.44/1.00  monotx_restored_types:                  0
% 3.44/1.00  sat_num_of_epr_types:                   0
% 3.44/1.00  sat_num_of_non_cyclic_types:            0
% 3.44/1.00  sat_guarded_non_collapsed_types:        0
% 3.44/1.00  num_pure_diseq_elim:                    0
% 3.44/1.00  simp_replaced_by:                       0
% 3.44/1.00  res_preprocessed:                       154
% 3.44/1.00  prep_upred:                             0
% 3.44/1.00  prep_unflattend:                        46
% 3.44/1.00  smt_new_axioms:                         0
% 3.44/1.00  pred_elim_cands:                        8
% 3.44/1.00  pred_elim:                              1
% 3.44/1.00  pred_elim_cl:                           1
% 3.44/1.00  pred_elim_cycles:                       7
% 3.44/1.00  merged_defs:                            0
% 3.44/1.00  merged_defs_ncl:                        0
% 3.44/1.00  bin_hyper_res:                          0
% 3.44/1.00  prep_cycles:                            4
% 3.44/1.00  pred_elim_time:                         0.014
% 3.44/1.00  splitting_time:                         0.
% 3.44/1.00  sem_filter_time:                        0.
% 3.44/1.00  monotx_time:                            0.001
% 3.44/1.00  subtype_inf_time:                       0.
% 3.44/1.00  
% 3.44/1.00  ------ Problem properties
% 3.44/1.00  
% 3.44/1.00  clauses:                                31
% 3.44/1.00  conjectures:                            10
% 3.44/1.00  epr:                                    6
% 3.44/1.00  horn:                                   29
% 3.44/1.00  ground:                                 10
% 3.44/1.00  unary:                                  13
% 3.44/1.00  binary:                                 4
% 3.44/1.00  lits:                                   89
% 3.44/1.00  lits_eq:                                16
% 3.44/1.00  fd_pure:                                0
% 3.44/1.00  fd_pseudo:                              0
% 3.44/1.00  fd_cond:                                1
% 3.44/1.00  fd_pseudo_cond:                         4
% 3.44/1.00  ac_symbols:                             0
% 3.44/1.00  
% 3.44/1.00  ------ Propositional Solver
% 3.44/1.00  
% 3.44/1.00  prop_solver_calls:                      27
% 3.44/1.00  prop_fast_solver_calls:                 1722
% 3.44/1.00  smt_solver_calls:                       0
% 3.44/1.00  smt_fast_solver_calls:                  0
% 3.44/1.00  prop_num_of_clauses:                    4734
% 3.44/1.00  prop_preprocess_simplified:             10756
% 3.44/1.00  prop_fo_subsumed:                       154
% 3.44/1.00  prop_solver_time:                       0.
% 3.44/1.00  smt_solver_time:                        0.
% 3.44/1.00  smt_fast_solver_time:                   0.
% 3.44/1.00  prop_fast_solver_time:                  0.
% 3.44/1.00  prop_unsat_core_time:                   0.
% 3.44/1.00  
% 3.44/1.00  ------ QBF
% 3.44/1.00  
% 3.44/1.00  qbf_q_res:                              0
% 3.44/1.00  qbf_num_tautologies:                    0
% 3.44/1.00  qbf_prep_cycles:                        0
% 3.44/1.00  
% 3.44/1.00  ------ BMC1
% 3.44/1.00  
% 3.44/1.00  bmc1_current_bound:                     -1
% 3.44/1.00  bmc1_last_solved_bound:                 -1
% 3.44/1.00  bmc1_unsat_core_size:                   -1
% 3.44/1.00  bmc1_unsat_core_parents_size:           -1
% 3.44/1.00  bmc1_merge_next_fun:                    0
% 3.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.44/1.00  
% 3.44/1.00  ------ Instantiation
% 3.44/1.00  
% 3.44/1.00  inst_num_of_clauses:                    1267
% 3.44/1.00  inst_num_in_passive:                    9
% 3.44/1.00  inst_num_in_active:                     762
% 3.44/1.00  inst_num_in_unprocessed:                496
% 3.44/1.00  inst_num_of_loops:                      790
% 3.44/1.00  inst_num_of_learning_restarts:          0
% 3.44/1.00  inst_num_moves_active_passive:          25
% 3.44/1.00  inst_lit_activity:                      0
% 3.44/1.00  inst_lit_activity_moves:                0
% 3.44/1.00  inst_num_tautologies:                   0
% 3.44/1.00  inst_num_prop_implied:                  0
% 3.44/1.00  inst_num_existing_simplified:           0
% 3.44/1.00  inst_num_eq_res_simplified:             0
% 3.44/1.00  inst_num_child_elim:                    0
% 3.44/1.00  inst_num_of_dismatching_blockings:      538
% 3.44/1.00  inst_num_of_non_proper_insts:           1990
% 3.44/1.00  inst_num_of_duplicates:                 0
% 3.44/1.00  inst_inst_num_from_inst_to_res:         0
% 3.44/1.00  inst_dismatching_checking_time:         0.
% 3.44/1.00  
% 3.44/1.00  ------ Resolution
% 3.44/1.00  
% 3.44/1.00  res_num_of_clauses:                     0
% 3.44/1.00  res_num_in_passive:                     0
% 3.44/1.00  res_num_in_active:                      0
% 3.44/1.00  res_num_of_loops:                       158
% 3.44/1.00  res_forward_subset_subsumed:            78
% 3.44/1.00  res_backward_subset_subsumed:           0
% 3.44/1.00  res_forward_subsumed:                   0
% 3.44/1.00  res_backward_subsumed:                  0
% 3.44/1.00  res_forward_subsumption_resolution:     2
% 3.44/1.00  res_backward_subsumption_resolution:    0
% 3.44/1.00  res_clause_to_clause_subsumption:       513
% 3.44/1.00  res_orphan_elimination:                 0
% 3.44/1.00  res_tautology_del:                      164
% 3.44/1.00  res_num_eq_res_simplified:              0
% 3.44/1.00  res_num_sel_changes:                    0
% 3.44/1.00  res_moves_from_active_to_pass:          0
% 3.44/1.00  
% 3.44/1.00  ------ Superposition
% 3.44/1.00  
% 3.44/1.00  sup_time_total:                         0.
% 3.44/1.00  sup_time_generating:                    0.
% 3.44/1.00  sup_time_sim_full:                      0.
% 3.44/1.00  sup_time_sim_immed:                     0.
% 3.44/1.00  
% 3.44/1.00  sup_num_of_clauses:                     140
% 3.44/1.00  sup_num_in_active:                      76
% 3.44/1.00  sup_num_in_passive:                     64
% 3.44/1.00  sup_num_of_loops:                       157
% 3.44/1.00  sup_fw_superposition:                   123
% 3.44/1.00  sup_bw_superposition:                   149
% 3.44/1.00  sup_immediate_simplified:               104
% 3.44/1.00  sup_given_eliminated:                   1
% 3.44/1.00  comparisons_done:                       0
% 3.44/1.00  comparisons_avoided:                    3
% 3.44/1.00  
% 3.44/1.00  ------ Simplifications
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  sim_fw_subset_subsumed:                 43
% 3.44/1.00  sim_bw_subset_subsumed:                 2
% 3.44/1.00  sim_fw_subsumed:                        7
% 3.44/1.00  sim_bw_subsumed:                        0
% 3.44/1.00  sim_fw_subsumption_res:                 3
% 3.44/1.00  sim_bw_subsumption_res:                 0
% 3.44/1.00  sim_tautology_del:                      2
% 3.44/1.00  sim_eq_tautology_del:                   20
% 3.44/1.00  sim_eq_res_simp:                        3
% 3.44/1.00  sim_fw_demodulated:                     29
% 3.44/1.00  sim_bw_demodulated:                     89
% 3.44/1.00  sim_light_normalised:                   39
% 3.44/1.00  sim_joinable_taut:                      0
% 3.44/1.00  sim_joinable_simp:                      0
% 3.44/1.00  sim_ac_normalised:                      0
% 3.44/1.00  sim_smt_subsumption:                    0
% 3.44/1.00  
%------------------------------------------------------------------------------
