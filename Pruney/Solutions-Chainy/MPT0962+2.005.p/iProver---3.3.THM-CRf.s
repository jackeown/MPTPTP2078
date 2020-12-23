%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:09 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  162 (1569 expanded)
%              Number of clauses        :   92 ( 565 expanded)
%              Number of leaves         :   20 ( 299 expanded)
%              Depth                    :   27
%              Number of atoms          :  460 (6573 expanded)
%              Number of equality atoms :  220 (1664 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f20,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f24,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK1(X0,X1),X0,X1)
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK1(X0,X1),X0,X1)
      & v1_funct_1(sK1(X0,X1))
      & v1_relat_1(sK1(X0,X1))
      & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f50])).

fof(f85,plain,(
    ! [X0,X1] : m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f41])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
        | ~ v1_funct_1(sK3) )
      & r1_tarski(k2_relat_1(sK3),sK2)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
      | ~ v1_funct_1(sK3) )
    & r1_tarski(k2_relat_1(sK3),sK2)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f52])).

fof(f92,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f98,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X0,X1] : v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_34,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1763,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2577,plain,
    ( m1_subset_1(sK1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1763])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1773,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3418,plain,
    ( r1_tarski(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_1773])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_279,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_280,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_342,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_280])).

cnf(c_455,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | X0 != X2
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_342])).

cnf(c_456,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_1760,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_5110,plain,
    ( sK1(k1_xboole_0,X0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3418,c_1760])).

cnf(c_5138,plain,
    ( sK1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5110])).

cnf(c_1774,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_201,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35,c_37])).

cnf(c_202,negated_conjecture,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK3) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_202])).

cnf(c_724,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relset_1(k1_relat_1(sK3),sK2,sK3) != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_732,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_724,c_22])).

cnf(c_1757,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_3667,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1757])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2067,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2096,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2097,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1150,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2090,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_2147,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_1149,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2148,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_3674,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3667,c_38,c_36,c_732,c_2096,c_2097,c_2147,c_2148])).

cnf(c_1762,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2663,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1760])).

cnf(c_3677,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3674,c_2663])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_130,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3871,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3677,c_130])).

cnf(c_17,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1770,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4270,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3871,c_1770])).

cnf(c_25,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_642,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_relat_1(sK3) != X0
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_202])).

cnf(c_643,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_1759,plain,
    ( sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1906,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1759,c_9])).

cnf(c_105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_107,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_117,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_119,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_1995,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1906,c_107,c_119])).

cnf(c_1996,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1995])).

cnf(c_3678,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3674,c_1996])).

cnf(c_3698,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3678])).

cnf(c_3702,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3698,c_9])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_591,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_592,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_4158,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3702,c_130,c_592,c_3677])).

cnf(c_4280,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4270,c_4158])).

cnf(c_4281,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_10])).

cnf(c_39,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4375,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4281,c_39])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1776,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4205,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1776])).

cnf(c_4381,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4375,c_4205])).

cnf(c_4389,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4381,c_1760])).

cnf(c_4396,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4389])).

cnf(c_4463,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4389,c_130,c_4396])).

cnf(c_31,plain,
    ( v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_736,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | sK1(X0,X1) != sK3
    | k1_relat_1(sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_202])).

cnf(c_737,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | sK1(k1_relat_1(sK3),sK2) != sK3 ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_1756,plain,
    ( sK1(k1_relat_1(sK3),sK2) != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_3681,plain,
    ( sK1(k1_relat_1(sK3),k1_xboole_0) != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3674,c_1756])).

cnf(c_3687,plain,
    ( sK1(k1_relat_1(sK3),k1_xboole_0) != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3681,c_9])).

cnf(c_4161,plain,
    ( sK1(k1_xboole_0,k1_xboole_0) != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4158,c_3687])).

cnf(c_4467,plain,
    ( sK1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4463,c_4161])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5138,c_4467,c_130,c_119,c_107])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:36:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.60/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/0.99  
% 2.60/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/0.99  
% 2.60/0.99  ------  iProver source info
% 2.60/0.99  
% 2.60/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.60/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/0.99  git: non_committed_changes: false
% 2.60/0.99  git: last_make_outside_of_git: false
% 2.60/0.99  
% 2.60/0.99  ------ 
% 2.60/0.99  
% 2.60/0.99  ------ Input Options
% 2.60/0.99  
% 2.60/0.99  --out_options                           all
% 2.60/0.99  --tptp_safe_out                         true
% 2.60/0.99  --problem_path                          ""
% 2.60/0.99  --include_path                          ""
% 2.60/0.99  --clausifier                            res/vclausify_rel
% 2.60/0.99  --clausifier_options                    --mode clausify
% 2.60/0.99  --stdin                                 false
% 2.60/0.99  --stats_out                             all
% 2.60/0.99  
% 2.60/0.99  ------ General Options
% 2.60/0.99  
% 2.60/0.99  --fof                                   false
% 2.60/0.99  --time_out_real                         305.
% 2.60/0.99  --time_out_virtual                      -1.
% 2.60/0.99  --symbol_type_check                     false
% 2.60/0.99  --clausify_out                          false
% 2.60/0.99  --sig_cnt_out                           false
% 2.60/0.99  --trig_cnt_out                          false
% 2.60/0.99  --trig_cnt_out_tolerance                1.
% 2.60/0.99  --trig_cnt_out_sk_spl                   false
% 2.60/0.99  --abstr_cl_out                          false
% 2.60/0.99  
% 2.60/0.99  ------ Global Options
% 2.60/0.99  
% 2.60/0.99  --schedule                              default
% 2.60/0.99  --add_important_lit                     false
% 2.60/0.99  --prop_solver_per_cl                    1000
% 2.60/0.99  --min_unsat_core                        false
% 2.60/0.99  --soft_assumptions                      false
% 2.60/0.99  --soft_lemma_size                       3
% 2.60/0.99  --prop_impl_unit_size                   0
% 2.60/0.99  --prop_impl_unit                        []
% 2.60/0.99  --share_sel_clauses                     true
% 2.60/0.99  --reset_solvers                         false
% 2.60/0.99  --bc_imp_inh                            [conj_cone]
% 2.60/0.99  --conj_cone_tolerance                   3.
% 2.60/0.99  --extra_neg_conj                        none
% 2.60/0.99  --large_theory_mode                     true
% 2.60/0.99  --prolific_symb_bound                   200
% 2.60/0.99  --lt_threshold                          2000
% 2.60/0.99  --clause_weak_htbl                      true
% 2.60/0.99  --gc_record_bc_elim                     false
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing Options
% 2.60/0.99  
% 2.60/0.99  --preprocessing_flag                    true
% 2.60/0.99  --time_out_prep_mult                    0.1
% 2.60/0.99  --splitting_mode                        input
% 2.60/0.99  --splitting_grd                         true
% 2.60/0.99  --splitting_cvd                         false
% 2.60/0.99  --splitting_cvd_svl                     false
% 2.60/0.99  --splitting_nvd                         32
% 2.60/0.99  --sub_typing                            true
% 2.60/0.99  --prep_gs_sim                           true
% 2.60/0.99  --prep_unflatten                        true
% 2.60/0.99  --prep_res_sim                          true
% 2.60/0.99  --prep_upred                            true
% 2.60/0.99  --prep_sem_filter                       exhaustive
% 2.60/0.99  --prep_sem_filter_out                   false
% 2.60/0.99  --pred_elim                             true
% 2.60/0.99  --res_sim_input                         true
% 2.60/0.99  --eq_ax_congr_red                       true
% 2.60/0.99  --pure_diseq_elim                       true
% 2.60/0.99  --brand_transform                       false
% 2.60/0.99  --non_eq_to_eq                          false
% 2.60/0.99  --prep_def_merge                        true
% 2.60/0.99  --prep_def_merge_prop_impl              false
% 2.60/0.99  --prep_def_merge_mbd                    true
% 2.60/0.99  --prep_def_merge_tr_red                 false
% 2.60/0.99  --prep_def_merge_tr_cl                  false
% 2.60/0.99  --smt_preprocessing                     true
% 2.60/0.99  --smt_ac_axioms                         fast
% 2.60/0.99  --preprocessed_out                      false
% 2.60/0.99  --preprocessed_stats                    false
% 2.60/0.99  
% 2.60/0.99  ------ Abstraction refinement Options
% 2.60/0.99  
% 2.60/0.99  --abstr_ref                             []
% 2.60/0.99  --abstr_ref_prep                        false
% 2.60/0.99  --abstr_ref_until_sat                   false
% 2.60/0.99  --abstr_ref_sig_restrict                funpre
% 2.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.99  --abstr_ref_under                       []
% 2.60/0.99  
% 2.60/0.99  ------ SAT Options
% 2.60/0.99  
% 2.60/0.99  --sat_mode                              false
% 2.60/0.99  --sat_fm_restart_options                ""
% 2.60/0.99  --sat_gr_def                            false
% 2.60/0.99  --sat_epr_types                         true
% 2.60/0.99  --sat_non_cyclic_types                  false
% 2.60/0.99  --sat_finite_models                     false
% 2.60/0.99  --sat_fm_lemmas                         false
% 2.60/0.99  --sat_fm_prep                           false
% 2.60/0.99  --sat_fm_uc_incr                        true
% 2.60/0.99  --sat_out_model                         small
% 2.60/0.99  --sat_out_clauses                       false
% 2.60/0.99  
% 2.60/0.99  ------ QBF Options
% 2.60/0.99  
% 2.60/0.99  --qbf_mode                              false
% 2.60/0.99  --qbf_elim_univ                         false
% 2.60/0.99  --qbf_dom_inst                          none
% 2.60/0.99  --qbf_dom_pre_inst                      false
% 2.60/0.99  --qbf_sk_in                             false
% 2.60/0.99  --qbf_pred_elim                         true
% 2.60/0.99  --qbf_split                             512
% 2.60/0.99  
% 2.60/0.99  ------ BMC1 Options
% 2.60/0.99  
% 2.60/0.99  --bmc1_incremental                      false
% 2.60/0.99  --bmc1_axioms                           reachable_all
% 2.60/0.99  --bmc1_min_bound                        0
% 2.60/0.99  --bmc1_max_bound                        -1
% 2.60/0.99  --bmc1_max_bound_default                -1
% 2.60/0.99  --bmc1_symbol_reachability              true
% 2.60/0.99  --bmc1_property_lemmas                  false
% 2.60/0.99  --bmc1_k_induction                      false
% 2.60/0.99  --bmc1_non_equiv_states                 false
% 2.60/0.99  --bmc1_deadlock                         false
% 2.60/0.99  --bmc1_ucm                              false
% 2.60/0.99  --bmc1_add_unsat_core                   none
% 2.60/0.99  --bmc1_unsat_core_children              false
% 2.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.99  --bmc1_out_stat                         full
% 2.60/0.99  --bmc1_ground_init                      false
% 2.60/0.99  --bmc1_pre_inst_next_state              false
% 2.60/0.99  --bmc1_pre_inst_state                   false
% 2.60/0.99  --bmc1_pre_inst_reach_state             false
% 2.60/0.99  --bmc1_out_unsat_core                   false
% 2.60/0.99  --bmc1_aig_witness_out                  false
% 2.60/0.99  --bmc1_verbose                          false
% 2.60/0.99  --bmc1_dump_clauses_tptp                false
% 2.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.99  --bmc1_dump_file                        -
% 2.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.99  --bmc1_ucm_extend_mode                  1
% 2.60/0.99  --bmc1_ucm_init_mode                    2
% 2.60/0.99  --bmc1_ucm_cone_mode                    none
% 2.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.99  --bmc1_ucm_relax_model                  4
% 2.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.99  --bmc1_ucm_layered_model                none
% 2.60/0.99  --bmc1_ucm_max_lemma_size               10
% 2.60/0.99  
% 2.60/0.99  ------ AIG Options
% 2.60/0.99  
% 2.60/0.99  --aig_mode                              false
% 2.60/0.99  
% 2.60/0.99  ------ Instantiation Options
% 2.60/0.99  
% 2.60/0.99  --instantiation_flag                    true
% 2.60/0.99  --inst_sos_flag                         false
% 2.60/0.99  --inst_sos_phase                        true
% 2.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.99  --inst_lit_sel_side                     num_symb
% 2.60/0.99  --inst_solver_per_active                1400
% 2.60/0.99  --inst_solver_calls_frac                1.
% 2.60/0.99  --inst_passive_queue_type               priority_queues
% 2.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.99  --inst_passive_queues_freq              [25;2]
% 2.60/0.99  --inst_dismatching                      true
% 2.60/0.99  --inst_eager_unprocessed_to_passive     true
% 2.60/0.99  --inst_prop_sim_given                   true
% 2.60/0.99  --inst_prop_sim_new                     false
% 2.60/0.99  --inst_subs_new                         false
% 2.60/0.99  --inst_eq_res_simp                      false
% 2.60/0.99  --inst_subs_given                       false
% 2.60/0.99  --inst_orphan_elimination               true
% 2.60/0.99  --inst_learning_loop_flag               true
% 2.60/0.99  --inst_learning_start                   3000
% 2.60/0.99  --inst_learning_factor                  2
% 2.60/0.99  --inst_start_prop_sim_after_learn       3
% 2.60/0.99  --inst_sel_renew                        solver
% 2.60/0.99  --inst_lit_activity_flag                true
% 2.60/0.99  --inst_restr_to_given                   false
% 2.60/0.99  --inst_activity_threshold               500
% 2.60/0.99  --inst_out_proof                        true
% 2.60/0.99  
% 2.60/0.99  ------ Resolution Options
% 2.60/0.99  
% 2.60/0.99  --resolution_flag                       true
% 2.60/0.99  --res_lit_sel                           adaptive
% 2.60/0.99  --res_lit_sel_side                      none
% 2.60/0.99  --res_ordering                          kbo
% 2.60/0.99  --res_to_prop_solver                    active
% 2.60/0.99  --res_prop_simpl_new                    false
% 2.60/0.99  --res_prop_simpl_given                  true
% 2.60/0.99  --res_passive_queue_type                priority_queues
% 2.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.99  --res_passive_queues_freq               [15;5]
% 2.60/0.99  --res_forward_subs                      full
% 2.60/0.99  --res_backward_subs                     full
% 2.60/0.99  --res_forward_subs_resolution           true
% 2.60/0.99  --res_backward_subs_resolution          true
% 2.60/0.99  --res_orphan_elimination                true
% 2.60/0.99  --res_time_limit                        2.
% 2.60/0.99  --res_out_proof                         true
% 2.60/0.99  
% 2.60/0.99  ------ Superposition Options
% 2.60/0.99  
% 2.60/0.99  --superposition_flag                    true
% 2.60/0.99  --sup_passive_queue_type                priority_queues
% 2.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.99  --demod_completeness_check              fast
% 2.60/0.99  --demod_use_ground                      true
% 2.60/0.99  --sup_to_prop_solver                    passive
% 2.60/0.99  --sup_prop_simpl_new                    true
% 2.60/0.99  --sup_prop_simpl_given                  true
% 2.60/0.99  --sup_fun_splitting                     false
% 2.60/0.99  --sup_smt_interval                      50000
% 2.60/0.99  
% 2.60/0.99  ------ Superposition Simplification Setup
% 2.60/0.99  
% 2.60/0.99  --sup_indices_passive                   []
% 2.60/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_full_bw                           [BwDemod]
% 2.60/0.99  --sup_immed_triv                        [TrivRules]
% 2.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_immed_bw_main                     []
% 2.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.99  
% 2.60/0.99  ------ Combination Options
% 2.60/0.99  
% 2.60/0.99  --comb_res_mult                         3
% 2.60/0.99  --comb_sup_mult                         2
% 2.60/0.99  --comb_inst_mult                        10
% 2.60/0.99  
% 2.60/0.99  ------ Debug Options
% 2.60/0.99  
% 2.60/0.99  --dbg_backtrace                         false
% 2.60/0.99  --dbg_dump_prop_clauses                 false
% 2.60/0.99  --dbg_dump_prop_clauses_file            -
% 2.60/0.99  --dbg_out_stat                          false
% 2.60/0.99  ------ Parsing...
% 2.60/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/0.99  ------ Proving...
% 2.60/0.99  ------ Problem Properties 
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  clauses                                 34
% 2.60/0.99  conjectures                             2
% 2.60/0.99  EPR                                     7
% 2.60/0.99  Horn                                    31
% 2.60/0.99  unary                                   13
% 2.60/0.99  binary                                  13
% 2.60/0.99  lits                                    67
% 2.60/0.99  lits eq                                 28
% 2.60/0.99  fd_pure                                 0
% 2.60/0.99  fd_pseudo                               0
% 2.60/0.99  fd_cond                                 4
% 2.60/0.99  fd_pseudo_cond                          1
% 2.60/0.99  AC symbols                              0
% 2.60/0.99  
% 2.60/0.99  ------ Schedule dynamic 5 is on 
% 2.60/0.99  
% 2.60/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  ------ 
% 2.60/0.99  Current options:
% 2.60/0.99  ------ 
% 2.60/0.99  
% 2.60/0.99  ------ Input Options
% 2.60/0.99  
% 2.60/0.99  --out_options                           all
% 2.60/0.99  --tptp_safe_out                         true
% 2.60/0.99  --problem_path                          ""
% 2.60/0.99  --include_path                          ""
% 2.60/0.99  --clausifier                            res/vclausify_rel
% 2.60/0.99  --clausifier_options                    --mode clausify
% 2.60/0.99  --stdin                                 false
% 2.60/0.99  --stats_out                             all
% 2.60/0.99  
% 2.60/0.99  ------ General Options
% 2.60/0.99  
% 2.60/0.99  --fof                                   false
% 2.60/0.99  --time_out_real                         305.
% 2.60/0.99  --time_out_virtual                      -1.
% 2.60/0.99  --symbol_type_check                     false
% 2.60/0.99  --clausify_out                          false
% 2.60/0.99  --sig_cnt_out                           false
% 2.60/0.99  --trig_cnt_out                          false
% 2.60/0.99  --trig_cnt_out_tolerance                1.
% 2.60/0.99  --trig_cnt_out_sk_spl                   false
% 2.60/0.99  --abstr_cl_out                          false
% 2.60/0.99  
% 2.60/0.99  ------ Global Options
% 2.60/0.99  
% 2.60/0.99  --schedule                              default
% 2.60/0.99  --add_important_lit                     false
% 2.60/0.99  --prop_solver_per_cl                    1000
% 2.60/0.99  --min_unsat_core                        false
% 2.60/0.99  --soft_assumptions                      false
% 2.60/0.99  --soft_lemma_size                       3
% 2.60/0.99  --prop_impl_unit_size                   0
% 2.60/0.99  --prop_impl_unit                        []
% 2.60/0.99  --share_sel_clauses                     true
% 2.60/0.99  --reset_solvers                         false
% 2.60/0.99  --bc_imp_inh                            [conj_cone]
% 2.60/0.99  --conj_cone_tolerance                   3.
% 2.60/0.99  --extra_neg_conj                        none
% 2.60/0.99  --large_theory_mode                     true
% 2.60/0.99  --prolific_symb_bound                   200
% 2.60/0.99  --lt_threshold                          2000
% 2.60/0.99  --clause_weak_htbl                      true
% 2.60/0.99  --gc_record_bc_elim                     false
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing Options
% 2.60/0.99  
% 2.60/0.99  --preprocessing_flag                    true
% 2.60/0.99  --time_out_prep_mult                    0.1
% 2.60/0.99  --splitting_mode                        input
% 2.60/0.99  --splitting_grd                         true
% 2.60/0.99  --splitting_cvd                         false
% 2.60/0.99  --splitting_cvd_svl                     false
% 2.60/0.99  --splitting_nvd                         32
% 2.60/0.99  --sub_typing                            true
% 2.60/0.99  --prep_gs_sim                           true
% 2.60/0.99  --prep_unflatten                        true
% 2.60/0.99  --prep_res_sim                          true
% 2.60/0.99  --prep_upred                            true
% 2.60/0.99  --prep_sem_filter                       exhaustive
% 2.60/0.99  --prep_sem_filter_out                   false
% 2.60/0.99  --pred_elim                             true
% 2.60/0.99  --res_sim_input                         true
% 2.60/0.99  --eq_ax_congr_red                       true
% 2.60/0.99  --pure_diseq_elim                       true
% 2.60/0.99  --brand_transform                       false
% 2.60/0.99  --non_eq_to_eq                          false
% 2.60/0.99  --prep_def_merge                        true
% 2.60/0.99  --prep_def_merge_prop_impl              false
% 2.60/0.99  --prep_def_merge_mbd                    true
% 2.60/0.99  --prep_def_merge_tr_red                 false
% 2.60/0.99  --prep_def_merge_tr_cl                  false
% 2.60/0.99  --smt_preprocessing                     true
% 2.60/0.99  --smt_ac_axioms                         fast
% 2.60/0.99  --preprocessed_out                      false
% 2.60/0.99  --preprocessed_stats                    false
% 2.60/0.99  
% 2.60/0.99  ------ Abstraction refinement Options
% 2.60/0.99  
% 2.60/0.99  --abstr_ref                             []
% 2.60/0.99  --abstr_ref_prep                        false
% 2.60/0.99  --abstr_ref_until_sat                   false
% 2.60/0.99  --abstr_ref_sig_restrict                funpre
% 2.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.99  --abstr_ref_under                       []
% 2.60/0.99  
% 2.60/0.99  ------ SAT Options
% 2.60/0.99  
% 2.60/0.99  --sat_mode                              false
% 2.60/0.99  --sat_fm_restart_options                ""
% 2.60/0.99  --sat_gr_def                            false
% 2.60/0.99  --sat_epr_types                         true
% 2.60/0.99  --sat_non_cyclic_types                  false
% 2.60/0.99  --sat_finite_models                     false
% 2.60/0.99  --sat_fm_lemmas                         false
% 2.60/0.99  --sat_fm_prep                           false
% 2.60/0.99  --sat_fm_uc_incr                        true
% 2.60/0.99  --sat_out_model                         small
% 2.60/0.99  --sat_out_clauses                       false
% 2.60/0.99  
% 2.60/0.99  ------ QBF Options
% 2.60/0.99  
% 2.60/0.99  --qbf_mode                              false
% 2.60/0.99  --qbf_elim_univ                         false
% 2.60/0.99  --qbf_dom_inst                          none
% 2.60/0.99  --qbf_dom_pre_inst                      false
% 2.60/0.99  --qbf_sk_in                             false
% 2.60/0.99  --qbf_pred_elim                         true
% 2.60/0.99  --qbf_split                             512
% 2.60/0.99  
% 2.60/0.99  ------ BMC1 Options
% 2.60/0.99  
% 2.60/0.99  --bmc1_incremental                      false
% 2.60/0.99  --bmc1_axioms                           reachable_all
% 2.60/0.99  --bmc1_min_bound                        0
% 2.60/0.99  --bmc1_max_bound                        -1
% 2.60/0.99  --bmc1_max_bound_default                -1
% 2.60/1.00  --bmc1_symbol_reachability              true
% 2.60/1.00  --bmc1_property_lemmas                  false
% 2.60/1.00  --bmc1_k_induction                      false
% 2.60/1.00  --bmc1_non_equiv_states                 false
% 2.60/1.00  --bmc1_deadlock                         false
% 2.60/1.00  --bmc1_ucm                              false
% 2.60/1.00  --bmc1_add_unsat_core                   none
% 2.60/1.00  --bmc1_unsat_core_children              false
% 2.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.00  --bmc1_out_stat                         full
% 2.60/1.00  --bmc1_ground_init                      false
% 2.60/1.00  --bmc1_pre_inst_next_state              false
% 2.60/1.00  --bmc1_pre_inst_state                   false
% 2.60/1.00  --bmc1_pre_inst_reach_state             false
% 2.60/1.00  --bmc1_out_unsat_core                   false
% 2.60/1.00  --bmc1_aig_witness_out                  false
% 2.60/1.00  --bmc1_verbose                          false
% 2.60/1.00  --bmc1_dump_clauses_tptp                false
% 2.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.00  --bmc1_dump_file                        -
% 2.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.00  --bmc1_ucm_extend_mode                  1
% 2.60/1.00  --bmc1_ucm_init_mode                    2
% 2.60/1.00  --bmc1_ucm_cone_mode                    none
% 2.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.00  --bmc1_ucm_relax_model                  4
% 2.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.00  --bmc1_ucm_layered_model                none
% 2.60/1.00  --bmc1_ucm_max_lemma_size               10
% 2.60/1.00  
% 2.60/1.00  ------ AIG Options
% 2.60/1.00  
% 2.60/1.00  --aig_mode                              false
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation Options
% 2.60/1.00  
% 2.60/1.00  --instantiation_flag                    true
% 2.60/1.00  --inst_sos_flag                         false
% 2.60/1.00  --inst_sos_phase                        true
% 2.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel_side                     none
% 2.60/1.00  --inst_solver_per_active                1400
% 2.60/1.00  --inst_solver_calls_frac                1.
% 2.60/1.00  --inst_passive_queue_type               priority_queues
% 2.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.00  --inst_passive_queues_freq              [25;2]
% 2.60/1.00  --inst_dismatching                      true
% 2.60/1.00  --inst_eager_unprocessed_to_passive     true
% 2.60/1.00  --inst_prop_sim_given                   true
% 2.60/1.00  --inst_prop_sim_new                     false
% 2.60/1.00  --inst_subs_new                         false
% 2.60/1.00  --inst_eq_res_simp                      false
% 2.60/1.00  --inst_subs_given                       false
% 2.60/1.00  --inst_orphan_elimination               true
% 2.60/1.00  --inst_learning_loop_flag               true
% 2.60/1.00  --inst_learning_start                   3000
% 2.60/1.00  --inst_learning_factor                  2
% 2.60/1.00  --inst_start_prop_sim_after_learn       3
% 2.60/1.00  --inst_sel_renew                        solver
% 2.60/1.00  --inst_lit_activity_flag                true
% 2.60/1.00  --inst_restr_to_given                   false
% 2.60/1.00  --inst_activity_threshold               500
% 2.60/1.00  --inst_out_proof                        true
% 2.60/1.00  
% 2.60/1.00  ------ Resolution Options
% 2.60/1.00  
% 2.60/1.00  --resolution_flag                       false
% 2.60/1.00  --res_lit_sel                           adaptive
% 2.60/1.00  --res_lit_sel_side                      none
% 2.60/1.00  --res_ordering                          kbo
% 2.60/1.00  --res_to_prop_solver                    active
% 2.60/1.00  --res_prop_simpl_new                    false
% 2.60/1.00  --res_prop_simpl_given                  true
% 2.60/1.00  --res_passive_queue_type                priority_queues
% 2.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.00  --res_passive_queues_freq               [15;5]
% 2.60/1.00  --res_forward_subs                      full
% 2.60/1.00  --res_backward_subs                     full
% 2.60/1.00  --res_forward_subs_resolution           true
% 2.60/1.00  --res_backward_subs_resolution          true
% 2.60/1.00  --res_orphan_elimination                true
% 2.60/1.00  --res_time_limit                        2.
% 2.60/1.00  --res_out_proof                         true
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Options
% 2.60/1.00  
% 2.60/1.00  --superposition_flag                    true
% 2.60/1.00  --sup_passive_queue_type                priority_queues
% 2.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.00  --demod_completeness_check              fast
% 2.60/1.00  --demod_use_ground                      true
% 2.60/1.00  --sup_to_prop_solver                    passive
% 2.60/1.00  --sup_prop_simpl_new                    true
% 2.60/1.00  --sup_prop_simpl_given                  true
% 2.60/1.00  --sup_fun_splitting                     false
% 2.60/1.00  --sup_smt_interval                      50000
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Simplification Setup
% 2.60/1.00  
% 2.60/1.00  --sup_indices_passive                   []
% 2.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_full_bw                           [BwDemod]
% 2.60/1.00  --sup_immed_triv                        [TrivRules]
% 2.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_immed_bw_main                     []
% 2.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  
% 2.60/1.00  ------ Combination Options
% 2.60/1.00  
% 2.60/1.00  --comb_res_mult                         3
% 2.60/1.00  --comb_sup_mult                         2
% 2.60/1.00  --comb_inst_mult                        10
% 2.60/1.00  
% 2.60/1.00  ------ Debug Options
% 2.60/1.00  
% 2.60/1.00  --dbg_backtrace                         false
% 2.60/1.00  --dbg_dump_prop_clauses                 false
% 2.60/1.00  --dbg_dump_prop_clauses_file            -
% 2.60/1.00  --dbg_out_stat                          false
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ Proving...
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS status Theorem for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  fof(f8,axiom,(
% 2.60/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f45,plain,(
% 2.60/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.60/1.00    inference(nnf_transformation,[],[f8])).
% 2.60/1.00  
% 2.60/1.00  fof(f46,plain,(
% 2.60/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.60/1.00    inference(flattening,[],[f45])).
% 2.60/1.00  
% 2.60/1.00  fof(f64,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.60/1.00    inference(cnf_transformation,[],[f46])).
% 2.60/1.00  
% 2.60/1.00  fof(f96,plain,(
% 2.60/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.60/1.00    inference(equality_resolution,[],[f64])).
% 2.60/1.00  
% 2.60/1.00  fof(f20,axiom,(
% 2.60/1.00    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f23,plain,(
% 2.60/1.00    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(pure_predicate_removal,[],[f20])).
% 2.60/1.00  
% 2.60/1.00  fof(f24,plain,(
% 2.60/1.00    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(pure_predicate_removal,[],[f23])).
% 2.60/1.00  
% 2.60/1.00  fof(f50,plain,(
% 2.60/1.00    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f51,plain,(
% 2.60/1.00    ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f50])).
% 2.60/1.00  
% 2.60/1.00  fof(f85,plain,(
% 2.60/1.00    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f51])).
% 2.60/1.00  
% 2.60/1.00  fof(f9,axiom,(
% 2.60/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f47,plain,(
% 2.60/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.60/1.00    inference(nnf_transformation,[],[f9])).
% 2.60/1.00  
% 2.60/1.00  fof(f66,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f47])).
% 2.60/1.00  
% 2.60/1.00  fof(f3,axiom,(
% 2.60/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f26,plain,(
% 2.60/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.60/1.00    inference(ennf_transformation,[],[f3])).
% 2.60/1.00  
% 2.60/1.00  fof(f41,plain,(
% 2.60/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f42,plain,(
% 2.60/1.00    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f41])).
% 2.60/1.00  
% 2.60/1.00  fof(f56,plain,(
% 2.60/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.60/1.00    inference(cnf_transformation,[],[f42])).
% 2.60/1.00  
% 2.60/1.00  fof(f10,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f29,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.60/1.00    inference(ennf_transformation,[],[f10])).
% 2.60/1.00  
% 2.60/1.00  fof(f68,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f29])).
% 2.60/1.00  
% 2.60/1.00  fof(f67,plain,(
% 2.60/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f47])).
% 2.60/1.00  
% 2.60/1.00  fof(f19,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f37,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(ennf_transformation,[],[f19])).
% 2.60/1.00  
% 2.60/1.00  fof(f38,plain,(
% 2.60/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(flattening,[],[f37])).
% 2.60/1.00  
% 2.60/1.00  fof(f49,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(nnf_transformation,[],[f38])).
% 2.60/1.00  
% 2.60/1.00  fof(f81,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f49])).
% 2.60/1.00  
% 2.60/1.00  fof(f21,conjecture,(
% 2.60/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f22,negated_conjecture,(
% 2.60/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.60/1.00    inference(negated_conjecture,[],[f21])).
% 2.60/1.00  
% 2.60/1.00  fof(f39,plain,(
% 2.60/1.00    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.60/1.00    inference(ennf_transformation,[],[f22])).
% 2.60/1.00  
% 2.60/1.00  fof(f40,plain,(
% 2.60/1.00    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.60/1.00    inference(flattening,[],[f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f52,plain,(
% 2.60/1.00    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f53,plain,(
% 2.60/1.00    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f52])).
% 2.60/1.00  
% 2.60/1.00  fof(f92,plain,(
% 2.60/1.00    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f90,plain,(
% 2.60/1.00    v1_funct_1(sK3)),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f16,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f34,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(ennf_transformation,[],[f16])).
% 2.60/1.00  
% 2.60/1.00  fof(f76,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f34])).
% 2.60/1.00  
% 2.60/1.00  fof(f89,plain,(
% 2.60/1.00    v1_relat_1(sK3)),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f91,plain,(
% 2.60/1.00    r1_tarski(k2_relat_1(sK3),sK2)),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f17,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f35,plain,(
% 2.60/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.60/1.00    inference(ennf_transformation,[],[f17])).
% 2.60/1.00  
% 2.60/1.00  fof(f36,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.60/1.00    inference(flattening,[],[f35])).
% 2.60/1.00  
% 2.60/1.00  fof(f77,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f36])).
% 2.60/1.00  
% 2.60/1.00  fof(f4,axiom,(
% 2.60/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f43,plain,(
% 2.60/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/1.00    inference(nnf_transformation,[],[f4])).
% 2.60/1.00  
% 2.60/1.00  fof(f44,plain,(
% 2.60/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/1.00    inference(flattening,[],[f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f57,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.60/1.00    inference(cnf_transformation,[],[f44])).
% 2.60/1.00  
% 2.60/1.00  fof(f94,plain,(
% 2.60/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.60/1.00    inference(equality_resolution,[],[f57])).
% 2.60/1.00  
% 2.60/1.00  fof(f1,axiom,(
% 2.60/1.00    v1_xboole_0(k1_xboole_0)),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f54,plain,(
% 2.60/1.00    v1_xboole_0(k1_xboole_0)),
% 2.60/1.00    inference(cnf_transformation,[],[f1])).
% 2.60/1.00  
% 2.60/1.00  fof(f13,axiom,(
% 2.60/1.00    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f32,plain,(
% 2.60/1.00    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f13])).
% 2.60/1.00  
% 2.60/1.00  fof(f71,plain,(
% 2.60/1.00    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f32])).
% 2.60/1.00  
% 2.60/1.00  fof(f84,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f49])).
% 2.60/1.00  
% 2.60/1.00  fof(f97,plain,(
% 2.60/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.00    inference(equality_resolution,[],[f84])).
% 2.60/1.00  
% 2.60/1.00  fof(f98,plain,(
% 2.60/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.60/1.00    inference(equality_resolution,[],[f97])).
% 2.60/1.00  
% 2.60/1.00  fof(f65,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.60/1.00    inference(cnf_transformation,[],[f46])).
% 2.60/1.00  
% 2.60/1.00  fof(f95,plain,(
% 2.60/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.60/1.00    inference(equality_resolution,[],[f65])).
% 2.60/1.00  
% 2.60/1.00  fof(f14,axiom,(
% 2.60/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f33,plain,(
% 2.60/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f14])).
% 2.60/1.00  
% 2.60/1.00  fof(f48,plain,(
% 2.60/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(nnf_transformation,[],[f33])).
% 2.60/1.00  
% 2.60/1.00  fof(f73,plain,(
% 2.60/1.00    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f48])).
% 2.60/1.00  
% 2.60/1.00  fof(f6,axiom,(
% 2.60/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f61,plain,(
% 2.60/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.60/1.00    inference(cnf_transformation,[],[f6])).
% 2.60/1.00  
% 2.60/1.00  fof(f5,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f27,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.60/1.00    inference(ennf_transformation,[],[f5])).
% 2.60/1.00  
% 2.60/1.00  fof(f60,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f27])).
% 2.60/1.00  
% 2.60/1.00  fof(f88,plain,(
% 2.60/1.00    ( ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f51])).
% 2.60/1.00  
% 2.60/1.00  cnf(c_10,plain,
% 2.60/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_34,plain,
% 2.60/1.00      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.60/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1763,plain,
% 2.60/1.00      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2577,plain,
% 2.60/1.00      ( m1_subset_1(sK1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_10,c_1763]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_13,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1773,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.60/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3418,plain,
% 2.60/1.00      ( r1_tarski(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_2577,c_1773]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2,plain,
% 2.60/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_14,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.60/1.00      | ~ r2_hidden(X2,X0)
% 2.60/1.00      | ~ v1_xboole_0(X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_12,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_279,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.60/1.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_280,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_279]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_342,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 2.60/1.00      inference(bin_hyper_res,[status(thm)],[c_14,c_280]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_455,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1)
% 2.60/1.00      | ~ v1_xboole_0(X1)
% 2.60/1.00      | X0 != X2
% 2.60/1.00      | sK0(X2) != X3
% 2.60/1.00      | k1_xboole_0 = X2 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_342]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_456,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | k1_xboole_0 = X0 ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1760,plain,
% 2.60/1.00      ( k1_xboole_0 = X0
% 2.60/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.60/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5110,plain,
% 2.60/1.00      ( sK1(k1_xboole_0,X0) = k1_xboole_0
% 2.60/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_3418,c_1760]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5138,plain,
% 2.60/1.00      ( sK1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.60/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_5110]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1774,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.60/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_28,plain,
% 2.60/1.00      ( v1_funct_2(X0,X1,X2)
% 2.60/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.60/1.00      | k1_xboole_0 = X2 ),
% 2.60/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_35,negated_conjecture,
% 2.60/1.00      ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
% 2.60/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | ~ v1_funct_1(sK3) ),
% 2.60/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_37,negated_conjecture,
% 2.60/1.00      ( v1_funct_1(sK3) ),
% 2.60/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_201,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_35,c_37]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_202,negated_conjecture,
% 2.60/1.00      ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
% 2.60/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_201]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_723,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.60/1.00      | k1_relat_1(sK3) != X1
% 2.60/1.00      | sK2 != X2
% 2.60/1.00      | sK3 != X0
% 2.60/1.00      | k1_xboole_0 = X2 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_202]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_724,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | k1_relset_1(k1_relat_1(sK3),sK2,sK3) != k1_relat_1(sK3)
% 2.60/1.00      | k1_xboole_0 = sK2 ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_723]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_22,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_732,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | k1_xboole_0 = sK2 ),
% 2.60/1.00      inference(forward_subsumption_resolution,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_724,c_22]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1757,plain,
% 2.60/1.00      ( k1_xboole_0 = sK2
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3667,plain,
% 2.60/1.00      ( sK2 = k1_xboole_0
% 2.60/1.00      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1774,c_1757]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_38,negated_conjecture,
% 2.60/1.00      ( v1_relat_1(sK3) ),
% 2.60/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_36,negated_conjecture,
% 2.60/1.00      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 2.60/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_23,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.60/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.60/1.00      | ~ v1_relat_1(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2067,plain,
% 2.60/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 2.60/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.60/1.00      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.60/1.00      | ~ v1_relat_1(sK3) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2096,plain,
% 2.60/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.60/1.00      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 2.60/1.00      | ~ v1_relat_1(sK3) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_2067]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5,plain,
% 2.60/1.00      ( r1_tarski(X0,X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2097,plain,
% 2.60/1.00      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1150,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2090,plain,
% 2.60/1.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_1150]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2147,plain,
% 2.60/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_2090]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1149,plain,( X0 = X0 ),theory(equality) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2148,plain,
% 2.60/1.00      ( sK2 = sK2 ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_1149]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3674,plain,
% 2.60/1.00      ( sK2 = k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_3667,c_38,c_36,c_732,c_2096,c_2097,c_2147,c_2148]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1762,plain,
% 2.60/1.00      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2663,plain,
% 2.60/1.00      ( k2_relat_1(sK3) = k1_xboole_0 | v1_xboole_0(sK2) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1762,c_1760]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3677,plain,
% 2.60/1.00      ( k2_relat_1(sK3) = k1_xboole_0
% 2.60/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_3674,c_2663]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_0,plain,
% 2.60/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_130,plain,
% 2.60/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3871,plain,
% 2.60/1.00      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_3677,c_130]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_17,plain,
% 2.60/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.60/1.00      | ~ v1_relat_1(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1770,plain,
% 2.60/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 2.60/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4270,plain,
% 2.60/1.00      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) = iProver_top
% 2.60/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_3871,c_1770]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_25,plain,
% 2.60/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.60/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.60/1.00      | k1_xboole_0 = X0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_642,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.60/1.00      | k1_relat_1(sK3) != X0
% 2.60/1.00      | sK2 != k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | k1_xboole_0 = X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_202]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_643,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 2.60/1.00      | sK2 != k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_642]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1759,plain,
% 2.60/1.00      ( sK2 != k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | k1_xboole_0 = k1_relat_1(sK3)
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 2.60/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_9,plain,
% 2.60/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1906,plain,
% 2.60/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 2.60/1.00      | sK2 != k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 2.60/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_1759,c_9]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_105,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.60/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_107,plain,
% 2.60/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.60/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_105]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_117,plain,
% 2.60/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_119,plain,
% 2.60/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_117]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1995,plain,
% 2.60/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | sK2 != k1_xboole_0
% 2.60/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1906,c_107,c_119]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1996,plain,
% 2.60/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 2.60/1.00      | sK2 != k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1995]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3678,plain,
% 2.60/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | k1_xboole_0 != k1_xboole_0
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_3674,c_1996]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3698,plain,
% 2.60/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
% 2.60/1.00      inference(equality_resolution_simp,[status(thm)],[c_3678]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3702,plain,
% 2.60/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 2.60/1.00      | sK3 != k1_xboole_0
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_3698,c_9]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_18,plain,
% 2.60/1.00      ( ~ v1_relat_1(X0)
% 2.60/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.60/1.00      | k1_relat_1(X0) = k1_xboole_0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_591,plain,
% 2.60/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 2.60/1.00      | k1_relat_1(X0) = k1_xboole_0
% 2.60/1.00      | sK3 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_592,plain,
% 2.60/1.00      ( k2_relat_1(sK3) != k1_xboole_0 | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_591]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4158,plain,
% 2.60/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_3702,c_130,c_592,c_3677]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4280,plain,
% 2.60/1.00      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 2.60/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.60/1.00      inference(light_normalisation,[status(thm)],[c_4270,c_4158]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4281,plain,
% 2.60/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 2.60/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_4280,c_10]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_39,plain,
% 2.60/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4375,plain,
% 2.60/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_4281,c_39]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_7,plain,
% 2.60/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_6,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 2.60/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1776,plain,
% 2.60/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.60/1.00      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4205,plain,
% 2.60/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.60/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_7,c_1776]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4381,plain,
% 2.60/1.00      ( r1_tarski(sK3,X0) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_4375,c_4205]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4389,plain,
% 2.60/1.00      ( sK3 = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_4381,c_1760]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4396,plain,
% 2.60/1.00      ( sK3 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_4389]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4463,plain,
% 2.60/1.00      ( sK3 = k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_4389,c_130,c_4396]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_31,plain,
% 2.60/1.00      ( v1_funct_2(sK1(X0,X1),X0,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_736,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | sK1(X0,X1) != sK3
% 2.60/1.00      | k1_relat_1(sK3) != X0
% 2.60/1.00      | sK2 != X1 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_202]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_737,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.60/1.00      | sK1(k1_relat_1(sK3),sK2) != sK3 ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_736]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1756,plain,
% 2.60/1.00      ( sK1(k1_relat_1(sK3),sK2) != sK3
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3681,plain,
% 2.60/1.00      ( sK1(k1_relat_1(sK3),k1_xboole_0) != sK3
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_3674,c_1756]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3687,plain,
% 2.60/1.00      ( sK1(k1_relat_1(sK3),k1_xboole_0) != sK3
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_3681,c_9]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4161,plain,
% 2.60/1.00      ( sK1(k1_xboole_0,k1_xboole_0) != sK3
% 2.60/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_4158,c_3687]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4467,plain,
% 2.60/1.00      ( sK1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.60/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_4463,c_4161]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(contradiction,plain,
% 2.60/1.00      ( $false ),
% 2.60/1.00      inference(minisat,[status(thm)],[c_5138,c_4467,c_130,c_119,c_107]) ).
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  ------                               Statistics
% 2.60/1.00  
% 2.60/1.00  ------ General
% 2.60/1.00  
% 2.60/1.00  abstr_ref_over_cycles:                  0
% 2.60/1.00  abstr_ref_under_cycles:                 0
% 2.60/1.00  gc_basic_clause_elim:                   0
% 2.60/1.00  forced_gc_time:                         0
% 2.60/1.00  parsing_time:                           0.01
% 2.60/1.00  unif_index_cands_time:                  0.
% 2.60/1.00  unif_index_add_time:                    0.
% 2.60/1.00  orderings_time:                         0.
% 2.60/1.00  out_proof_time:                         0.014
% 2.60/1.00  total_time:                             0.166
% 2.60/1.00  num_of_symbols:                         50
% 2.60/1.00  num_of_terms:                           4404
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing
% 2.60/1.00  
% 2.60/1.00  num_of_splits:                          0
% 2.60/1.00  num_of_split_atoms:                     0
% 2.60/1.00  num_of_reused_defs:                     0
% 2.60/1.00  num_eq_ax_congr_red:                    12
% 2.60/1.00  num_of_sem_filtered_clauses:            3
% 2.60/1.00  num_of_subtypes:                        0
% 2.60/1.00  monotx_restored_types:                  0
% 2.60/1.00  sat_num_of_epr_types:                   0
% 2.60/1.00  sat_num_of_non_cyclic_types:            0
% 2.60/1.00  sat_guarded_non_collapsed_types:        0
% 2.60/1.00  num_pure_diseq_elim:                    0
% 2.60/1.00  simp_replaced_by:                       0
% 2.60/1.00  res_preprocessed:                       167
% 2.60/1.00  prep_upred:                             0
% 2.60/1.00  prep_unflattend:                        55
% 2.60/1.00  smt_new_axioms:                         0
% 2.60/1.00  pred_elim_cands:                        4
% 2.60/1.00  pred_elim:                              2
% 2.60/1.00  pred_elim_cl:                           2
% 2.60/1.00  pred_elim_cycles:                       5
% 2.60/1.00  merged_defs:                            8
% 2.60/1.00  merged_defs_ncl:                        0
% 2.60/1.00  bin_hyper_res:                          9
% 2.60/1.00  prep_cycles:                            4
% 2.60/1.00  pred_elim_time:                         0.009
% 2.60/1.00  splitting_time:                         0.
% 2.60/1.00  sem_filter_time:                        0.
% 2.60/1.00  monotx_time:                            0.
% 2.60/1.00  subtype_inf_time:                       0.
% 2.60/1.00  
% 2.60/1.00  ------ Problem properties
% 2.60/1.00  
% 2.60/1.00  clauses:                                34
% 2.60/1.00  conjectures:                            2
% 2.60/1.00  epr:                                    7
% 2.60/1.00  horn:                                   31
% 2.60/1.00  ground:                                 7
% 2.60/1.00  unary:                                  13
% 2.60/1.00  binary:                                 13
% 2.60/1.00  lits:                                   67
% 2.60/1.00  lits_eq:                                28
% 2.60/1.00  fd_pure:                                0
% 2.60/1.00  fd_pseudo:                              0
% 2.60/1.00  fd_cond:                                4
% 2.60/1.00  fd_pseudo_cond:                         1
% 2.60/1.00  ac_symbols:                             0
% 2.60/1.00  
% 2.60/1.00  ------ Propositional Solver
% 2.60/1.00  
% 2.60/1.00  prop_solver_calls:                      27
% 2.60/1.00  prop_fast_solver_calls:                 916
% 2.60/1.00  smt_solver_calls:                       0
% 2.60/1.00  smt_fast_solver_calls:                  0
% 2.60/1.00  prop_num_of_clauses:                    1807
% 2.60/1.00  prop_preprocess_simplified:             6116
% 2.60/1.00  prop_fo_subsumed:                       12
% 2.60/1.00  prop_solver_time:                       0.
% 2.60/1.00  smt_solver_time:                        0.
% 2.60/1.00  smt_fast_solver_time:                   0.
% 2.60/1.00  prop_fast_solver_time:                  0.
% 2.60/1.00  prop_unsat_core_time:                   0.
% 2.60/1.00  
% 2.60/1.00  ------ QBF
% 2.60/1.00  
% 2.60/1.00  qbf_q_res:                              0
% 2.60/1.00  qbf_num_tautologies:                    0
% 2.60/1.00  qbf_prep_cycles:                        0
% 2.60/1.00  
% 2.60/1.00  ------ BMC1
% 2.60/1.00  
% 2.60/1.00  bmc1_current_bound:                     -1
% 2.60/1.00  bmc1_last_solved_bound:                 -1
% 2.60/1.00  bmc1_unsat_core_size:                   -1
% 2.60/1.00  bmc1_unsat_core_parents_size:           -1
% 2.60/1.00  bmc1_merge_next_fun:                    0
% 2.60/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation
% 2.60/1.00  
% 2.60/1.00  inst_num_of_clauses:                    515
% 2.60/1.00  inst_num_in_passive:                    142
% 2.60/1.00  inst_num_in_active:                     254
% 2.60/1.00  inst_num_in_unprocessed:                121
% 2.60/1.00  inst_num_of_loops:                      330
% 2.60/1.00  inst_num_of_learning_restarts:          0
% 2.60/1.00  inst_num_moves_active_passive:          73
% 2.60/1.00  inst_lit_activity:                      0
% 2.60/1.00  inst_lit_activity_moves:                0
% 2.60/1.00  inst_num_tautologies:                   0
% 2.60/1.00  inst_num_prop_implied:                  0
% 2.60/1.00  inst_num_existing_simplified:           0
% 2.60/1.00  inst_num_eq_res_simplified:             0
% 2.60/1.00  inst_num_child_elim:                    0
% 2.60/1.00  inst_num_of_dismatching_blockings:      150
% 2.60/1.00  inst_num_of_non_proper_insts:           559
% 2.60/1.00  inst_num_of_duplicates:                 0
% 2.60/1.00  inst_inst_num_from_inst_to_res:         0
% 2.60/1.00  inst_dismatching_checking_time:         0.
% 2.60/1.00  
% 2.60/1.00  ------ Resolution
% 2.60/1.00  
% 2.60/1.00  res_num_of_clauses:                     0
% 2.60/1.00  res_num_in_passive:                     0
% 2.60/1.00  res_num_in_active:                      0
% 2.60/1.00  res_num_of_loops:                       171
% 2.60/1.00  res_forward_subset_subsumed:            34
% 2.60/1.00  res_backward_subset_subsumed:           4
% 2.60/1.00  res_forward_subsumed:                   0
% 2.60/1.00  res_backward_subsumed:                  0
% 2.60/1.00  res_forward_subsumption_resolution:     3
% 2.60/1.00  res_backward_subsumption_resolution:    0
% 2.60/1.00  res_clause_to_clause_subsumption:       310
% 2.60/1.00  res_orphan_elimination:                 0
% 2.60/1.00  res_tautology_del:                      53
% 2.60/1.00  res_num_eq_res_simplified:              0
% 2.60/1.00  res_num_sel_changes:                    0
% 2.60/1.00  res_moves_from_active_to_pass:          0
% 2.60/1.00  
% 2.60/1.00  ------ Superposition
% 2.60/1.00  
% 2.60/1.00  sup_time_total:                         0.
% 2.60/1.00  sup_time_generating:                    0.
% 2.60/1.00  sup_time_sim_full:                      0.
% 2.60/1.00  sup_time_sim_immed:                     0.
% 2.60/1.00  
% 2.60/1.00  sup_num_of_clauses:                     74
% 2.60/1.00  sup_num_in_active:                      47
% 2.60/1.00  sup_num_in_passive:                     27
% 2.60/1.00  sup_num_of_loops:                       64
% 2.60/1.00  sup_fw_superposition:                   53
% 2.60/1.00  sup_bw_superposition:                   36
% 2.60/1.00  sup_immediate_simplified:               28
% 2.60/1.00  sup_given_eliminated:                   4
% 2.60/1.00  comparisons_done:                       0
% 2.60/1.00  comparisons_avoided:                    0
% 2.60/1.00  
% 2.60/1.00  ------ Simplifications
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  sim_fw_subset_subsumed:                 9
% 2.60/1.00  sim_bw_subset_subsumed:                 2
% 2.60/1.00  sim_fw_subsumed:                        8
% 2.60/1.00  sim_bw_subsumed:                        4
% 2.60/1.00  sim_fw_subsumption_res:                 0
% 2.60/1.00  sim_bw_subsumption_res:                 0
% 2.60/1.00  sim_tautology_del:                      3
% 2.60/1.00  sim_eq_tautology_del:                   7
% 2.60/1.00  sim_eq_res_simp:                        1
% 2.60/1.00  sim_fw_demodulated:                     12
% 2.60/1.00  sim_bw_demodulated:                     14
% 2.60/1.00  sim_light_normalised:                   7
% 2.60/1.00  sim_joinable_taut:                      0
% 2.60/1.00  sim_joinable_simp:                      0
% 2.60/1.00  sim_ac_normalised:                      0
% 2.60/1.00  sim_smt_subsumption:                    0
% 2.60/1.00  
%------------------------------------------------------------------------------
