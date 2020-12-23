%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:34 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  296 (12033 expanded)
%              Number of clauses        :  211 (5141 expanded)
%              Number of leaves         :   26 (2179 expanded)
%              Depth                    :   35
%              Number of atoms          :  858 (49673 expanded)
%              Number of equality atoms :  532 (18109 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f51])).

fof(f86,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f42])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_582,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_584,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_35])).

cnf(c_1515,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1519,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3857,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1515,c_1519])).

cnf(c_4041,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_584,c_3857])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_16])).

cnf(c_1512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_1849,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_1512])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1518,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3590,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1515,c_1518])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1516,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3895,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3590,c_1516])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3856,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1519])).

cnf(c_27738,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3895,c_3856])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1525,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2988,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_1525])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_273,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_273])).

cnf(c_336,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_274])).

cnf(c_1514,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_3232,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2988,c_1514])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1523,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3367,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3232,c_1523])).

cnf(c_29354,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27738,c_3367])).

cnf(c_29355,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29354])).

cnf(c_29365,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_29355])).

cnf(c_29515,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29365,c_3367])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_195,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_37])).

cnf(c_196,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_196])).

cnf(c_569,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_1507,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_29518,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29515,c_1507])).

cnf(c_2184,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2185,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2184])).

cnf(c_29521,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29518,c_1849,c_2185,c_3367,c_3895])).

cnf(c_29522,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_29521])).

cnf(c_29525,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4041,c_29522])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_29702,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29525,c_33])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_881,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2098,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2731,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2734,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_3368,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3367])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_274])).

cnf(c_452,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | X0 != X2
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_335])).

cnf(c_453,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_1513,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_2349,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1513])).

cnf(c_3894,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3590,c_2349])).

cnf(c_3907,plain,
    ( ~ v1_xboole_0(sK3)
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3894])).

cnf(c_883,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4513,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_4515,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4513])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5497,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_884,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2551,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_5133,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2551])).

cnf(c_10467,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,sK4)
    | X0 != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5133])).

cnf(c_10468,plain,
    ( X0 != sK4
    | sK4 != sK4
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10467])).

cnf(c_10470,plain,
    ( sK4 != sK4
    | k1_xboole_0 != sK4
    | r1_tarski(sK4,sK4) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10468])).

cnf(c_1526,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1852,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1512])).

cnf(c_4642,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_1852])).

cnf(c_2994,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_1512])).

cnf(c_9914,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_2994])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5212,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2994])).

cnf(c_5279,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5212,c_1514])).

cnf(c_82,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1752,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_1870,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_1872,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1871,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1874,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1871])).

cnf(c_12755,plain,
    ( v1_relat_1(k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5279,c_82,c_1872,c_1874])).

cnf(c_12756,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12755])).

cnf(c_22404,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9914,c_12756])).

cnf(c_22405,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22404])).

cnf(c_22414,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4041,c_22405])).

cnf(c_5277,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4041,c_5212])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_109,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_111,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_1826,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_1827,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_1829,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_520,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_1510,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_1640,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1510,c_8])).

cnf(c_882,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1775,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_1834,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_1835,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_2053,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_2054,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2053])).

cnf(c_2180,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1640,c_33,c_104,c_105,c_1834,c_1835,c_2054])).

cnf(c_5750,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5277,c_104,c_105,c_111,c_1829,c_2180,c_3367])).

cnf(c_5751,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5750])).

cnf(c_3553,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1517])).

cnf(c_5578,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4041,c_3553])).

cnf(c_101,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_103,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_886,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_895,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2015,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2019,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_2350,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1513])).

cnf(c_2369,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_xboole_0(sK1)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2350])).

cnf(c_2663,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_2665,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2663])).

cnf(c_2103,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_2825,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2103])).

cnf(c_2826,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_887,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1795,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_2004,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_3778,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK4,k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_3779,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | sK4 != X2
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3778])).

cnf(c_3781,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3779])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5496,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_5506,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5496])).

cnf(c_5903,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5578,c_103,c_104,c_105,c_111,c_0,c_895,c_1834,c_1835,c_2019,c_2098,c_2369,c_2665,c_2826,c_3367,c_3368,c_3781,c_5506])).

cnf(c_5904,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5903])).

cnf(c_5910,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5904,c_1852])).

cnf(c_6698,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5910,c_3367])).

cnf(c_6699,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6698])).

cnf(c_6711,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6699,c_2994])).

cnf(c_6708,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6699,c_1514])).

cnf(c_6761,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6708])).

cnf(c_7676,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6711,c_82,c_1872,c_1874,c_6761])).

cnf(c_7677,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7676])).

cnf(c_7684,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4041,c_7677])).

cnf(c_23244,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22414,c_104,c_105,c_111,c_1829,c_2180,c_3367,c_5277,c_7684])).

cnf(c_23245,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_23244])).

cnf(c_1529,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3554,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1525])).

cnf(c_6308,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_1513])).

cnf(c_16532,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,k2_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_6308])).

cnf(c_20466,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_16532])).

cnf(c_121,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_21451,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20466,c_121])).

cnf(c_21452,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_21451])).

cnf(c_23268,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_23245,c_21452])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1764,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1765,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1764])).

cnf(c_6954,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6957,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6954])).

cnf(c_23956,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23268,c_104,c_105,c_111,c_1765,c_1829,c_2180,c_3367,c_5277,c_6957])).

cnf(c_23957,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_23956])).

cnf(c_29743,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29702,c_0,c_2098,c_2734,c_3368,c_3907,c_4515,c_5497,c_10470,c_23957])).

cnf(c_29747,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_29743,c_29515])).

cnf(c_29877,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_29743,c_3857])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_36])).

cnf(c_556,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_1508,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_1633,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1508,c_9])).

cnf(c_29888,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29743,c_1633])).

cnf(c_29905,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_29888])).

cnf(c_29891,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_29743,c_1515])).

cnf(c_29894,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_29891,c_9])).

cnf(c_29908,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29905,c_29894])).

cnf(c_29946,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_29877,c_29908])).

cnf(c_30399,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_29747,c_29946])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_196])).

cnf(c_540,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_1509,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_1663,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1509,c_9])).

cnf(c_29887,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29743,c_1663])).

cnf(c_29910,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_29887])).

cnf(c_29914,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29910,c_29894])).

cnf(c_29915,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29914,c_9])).

cnf(c_30401,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30399,c_29915])).

cnf(c_30403,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_30401])).

cnf(c_30405,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_30403,c_29894])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.94/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.94/1.50  
% 6.94/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.94/1.50  
% 6.94/1.50  ------  iProver source info
% 6.94/1.50  
% 6.94/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.94/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.94/1.50  git: non_committed_changes: false
% 6.94/1.50  git: last_make_outside_of_git: false
% 6.94/1.50  
% 6.94/1.50  ------ 
% 6.94/1.50  
% 6.94/1.50  ------ Input Options
% 6.94/1.50  
% 6.94/1.50  --out_options                           all
% 6.94/1.50  --tptp_safe_out                         true
% 6.94/1.50  --problem_path                          ""
% 6.94/1.50  --include_path                          ""
% 6.94/1.50  --clausifier                            res/vclausify_rel
% 6.94/1.50  --clausifier_options                    --mode clausify
% 6.94/1.50  --stdin                                 false
% 6.94/1.50  --stats_out                             all
% 6.94/1.50  
% 6.94/1.50  ------ General Options
% 6.94/1.50  
% 6.94/1.50  --fof                                   false
% 6.94/1.50  --time_out_real                         305.
% 6.94/1.50  --time_out_virtual                      -1.
% 6.94/1.50  --symbol_type_check                     false
% 6.94/1.50  --clausify_out                          false
% 6.94/1.50  --sig_cnt_out                           false
% 6.94/1.50  --trig_cnt_out                          false
% 6.94/1.50  --trig_cnt_out_tolerance                1.
% 6.94/1.50  --trig_cnt_out_sk_spl                   false
% 6.94/1.50  --abstr_cl_out                          false
% 6.94/1.50  
% 6.94/1.50  ------ Global Options
% 6.94/1.50  
% 6.94/1.50  --schedule                              default
% 6.94/1.50  --add_important_lit                     false
% 6.94/1.50  --prop_solver_per_cl                    1000
% 6.94/1.50  --min_unsat_core                        false
% 6.94/1.50  --soft_assumptions                      false
% 6.94/1.50  --soft_lemma_size                       3
% 6.94/1.50  --prop_impl_unit_size                   0
% 6.94/1.50  --prop_impl_unit                        []
% 6.94/1.50  --share_sel_clauses                     true
% 6.94/1.50  --reset_solvers                         false
% 6.94/1.50  --bc_imp_inh                            [conj_cone]
% 6.94/1.50  --conj_cone_tolerance                   3.
% 6.94/1.50  --extra_neg_conj                        none
% 6.94/1.50  --large_theory_mode                     true
% 6.94/1.50  --prolific_symb_bound                   200
% 6.94/1.50  --lt_threshold                          2000
% 6.94/1.50  --clause_weak_htbl                      true
% 6.94/1.50  --gc_record_bc_elim                     false
% 6.94/1.50  
% 6.94/1.50  ------ Preprocessing Options
% 6.94/1.50  
% 6.94/1.50  --preprocessing_flag                    true
% 6.94/1.50  --time_out_prep_mult                    0.1
% 6.94/1.50  --splitting_mode                        input
% 6.94/1.50  --splitting_grd                         true
% 6.94/1.50  --splitting_cvd                         false
% 6.94/1.50  --splitting_cvd_svl                     false
% 6.94/1.50  --splitting_nvd                         32
% 6.94/1.50  --sub_typing                            true
% 6.94/1.50  --prep_gs_sim                           true
% 6.94/1.50  --prep_unflatten                        true
% 6.94/1.50  --prep_res_sim                          true
% 6.94/1.50  --prep_upred                            true
% 6.94/1.50  --prep_sem_filter                       exhaustive
% 6.94/1.50  --prep_sem_filter_out                   false
% 6.94/1.50  --pred_elim                             true
% 6.94/1.50  --res_sim_input                         true
% 6.94/1.50  --eq_ax_congr_red                       true
% 6.94/1.50  --pure_diseq_elim                       true
% 6.94/1.50  --brand_transform                       false
% 6.94/1.50  --non_eq_to_eq                          false
% 6.94/1.50  --prep_def_merge                        true
% 6.94/1.50  --prep_def_merge_prop_impl              false
% 6.94/1.50  --prep_def_merge_mbd                    true
% 6.94/1.50  --prep_def_merge_tr_red                 false
% 6.94/1.50  --prep_def_merge_tr_cl                  false
% 6.94/1.50  --smt_preprocessing                     true
% 6.94/1.50  --smt_ac_axioms                         fast
% 6.94/1.50  --preprocessed_out                      false
% 6.94/1.50  --preprocessed_stats                    false
% 6.94/1.50  
% 6.94/1.50  ------ Abstraction refinement Options
% 6.94/1.50  
% 6.94/1.50  --abstr_ref                             []
% 6.94/1.50  --abstr_ref_prep                        false
% 6.94/1.50  --abstr_ref_until_sat                   false
% 6.94/1.50  --abstr_ref_sig_restrict                funpre
% 6.94/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.94/1.50  --abstr_ref_under                       []
% 6.94/1.50  
% 6.94/1.50  ------ SAT Options
% 6.94/1.50  
% 6.94/1.50  --sat_mode                              false
% 6.94/1.50  --sat_fm_restart_options                ""
% 6.94/1.50  --sat_gr_def                            false
% 6.94/1.50  --sat_epr_types                         true
% 6.94/1.50  --sat_non_cyclic_types                  false
% 6.94/1.50  --sat_finite_models                     false
% 6.94/1.50  --sat_fm_lemmas                         false
% 6.94/1.50  --sat_fm_prep                           false
% 6.94/1.50  --sat_fm_uc_incr                        true
% 6.94/1.50  --sat_out_model                         small
% 6.94/1.50  --sat_out_clauses                       false
% 6.94/1.50  
% 6.94/1.50  ------ QBF Options
% 6.94/1.50  
% 6.94/1.50  --qbf_mode                              false
% 6.94/1.50  --qbf_elim_univ                         false
% 6.94/1.50  --qbf_dom_inst                          none
% 6.94/1.50  --qbf_dom_pre_inst                      false
% 6.94/1.50  --qbf_sk_in                             false
% 6.94/1.50  --qbf_pred_elim                         true
% 6.94/1.50  --qbf_split                             512
% 6.94/1.50  
% 6.94/1.50  ------ BMC1 Options
% 6.94/1.50  
% 6.94/1.50  --bmc1_incremental                      false
% 6.94/1.50  --bmc1_axioms                           reachable_all
% 6.94/1.50  --bmc1_min_bound                        0
% 6.94/1.50  --bmc1_max_bound                        -1
% 6.94/1.50  --bmc1_max_bound_default                -1
% 6.94/1.50  --bmc1_symbol_reachability              true
% 6.94/1.50  --bmc1_property_lemmas                  false
% 6.94/1.50  --bmc1_k_induction                      false
% 6.94/1.50  --bmc1_non_equiv_states                 false
% 6.94/1.50  --bmc1_deadlock                         false
% 6.94/1.50  --bmc1_ucm                              false
% 6.94/1.50  --bmc1_add_unsat_core                   none
% 6.94/1.50  --bmc1_unsat_core_children              false
% 6.94/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.94/1.50  --bmc1_out_stat                         full
% 6.94/1.50  --bmc1_ground_init                      false
% 6.94/1.50  --bmc1_pre_inst_next_state              false
% 6.94/1.50  --bmc1_pre_inst_state                   false
% 6.94/1.50  --bmc1_pre_inst_reach_state             false
% 6.94/1.50  --bmc1_out_unsat_core                   false
% 6.94/1.50  --bmc1_aig_witness_out                  false
% 6.94/1.50  --bmc1_verbose                          false
% 6.94/1.50  --bmc1_dump_clauses_tptp                false
% 6.94/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.94/1.50  --bmc1_dump_file                        -
% 6.94/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.94/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.94/1.50  --bmc1_ucm_extend_mode                  1
% 6.94/1.50  --bmc1_ucm_init_mode                    2
% 6.94/1.50  --bmc1_ucm_cone_mode                    none
% 6.94/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.94/1.50  --bmc1_ucm_relax_model                  4
% 6.94/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.94/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.94/1.50  --bmc1_ucm_layered_model                none
% 6.94/1.50  --bmc1_ucm_max_lemma_size               10
% 6.94/1.50  
% 6.94/1.50  ------ AIG Options
% 6.94/1.50  
% 6.94/1.50  --aig_mode                              false
% 6.94/1.50  
% 6.94/1.50  ------ Instantiation Options
% 6.94/1.50  
% 6.94/1.50  --instantiation_flag                    true
% 6.94/1.50  --inst_sos_flag                         false
% 6.94/1.50  --inst_sos_phase                        true
% 6.94/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.94/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.94/1.50  --inst_lit_sel_side                     num_symb
% 6.94/1.50  --inst_solver_per_active                1400
% 6.94/1.50  --inst_solver_calls_frac                1.
% 6.94/1.50  --inst_passive_queue_type               priority_queues
% 6.94/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.94/1.50  --inst_passive_queues_freq              [25;2]
% 6.94/1.50  --inst_dismatching                      true
% 6.94/1.50  --inst_eager_unprocessed_to_passive     true
% 6.94/1.50  --inst_prop_sim_given                   true
% 6.94/1.50  --inst_prop_sim_new                     false
% 6.94/1.50  --inst_subs_new                         false
% 6.94/1.50  --inst_eq_res_simp                      false
% 6.94/1.50  --inst_subs_given                       false
% 6.94/1.50  --inst_orphan_elimination               true
% 6.94/1.50  --inst_learning_loop_flag               true
% 6.94/1.50  --inst_learning_start                   3000
% 6.94/1.50  --inst_learning_factor                  2
% 6.94/1.50  --inst_start_prop_sim_after_learn       3
% 6.94/1.50  --inst_sel_renew                        solver
% 6.94/1.50  --inst_lit_activity_flag                true
% 6.94/1.50  --inst_restr_to_given                   false
% 6.94/1.50  --inst_activity_threshold               500
% 6.94/1.50  --inst_out_proof                        true
% 6.94/1.50  
% 6.94/1.50  ------ Resolution Options
% 6.94/1.50  
% 6.94/1.50  --resolution_flag                       true
% 6.94/1.50  --res_lit_sel                           adaptive
% 6.94/1.50  --res_lit_sel_side                      none
% 6.94/1.50  --res_ordering                          kbo
% 6.94/1.50  --res_to_prop_solver                    active
% 6.94/1.50  --res_prop_simpl_new                    false
% 6.94/1.50  --res_prop_simpl_given                  true
% 6.94/1.50  --res_passive_queue_type                priority_queues
% 6.94/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.94/1.50  --res_passive_queues_freq               [15;5]
% 6.94/1.50  --res_forward_subs                      full
% 6.94/1.50  --res_backward_subs                     full
% 6.94/1.50  --res_forward_subs_resolution           true
% 6.94/1.50  --res_backward_subs_resolution          true
% 6.94/1.50  --res_orphan_elimination                true
% 6.94/1.50  --res_time_limit                        2.
% 6.94/1.50  --res_out_proof                         true
% 6.94/1.50  
% 6.94/1.50  ------ Superposition Options
% 6.94/1.50  
% 6.94/1.50  --superposition_flag                    true
% 6.94/1.50  --sup_passive_queue_type                priority_queues
% 6.94/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.94/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.94/1.50  --demod_completeness_check              fast
% 6.94/1.50  --demod_use_ground                      true
% 6.94/1.50  --sup_to_prop_solver                    passive
% 6.94/1.50  --sup_prop_simpl_new                    true
% 6.94/1.50  --sup_prop_simpl_given                  true
% 6.94/1.50  --sup_fun_splitting                     false
% 6.94/1.50  --sup_smt_interval                      50000
% 6.94/1.50  
% 6.94/1.50  ------ Superposition Simplification Setup
% 6.94/1.50  
% 6.94/1.50  --sup_indices_passive                   []
% 6.94/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.94/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.50  --sup_full_bw                           [BwDemod]
% 6.94/1.50  --sup_immed_triv                        [TrivRules]
% 6.94/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.50  --sup_immed_bw_main                     []
% 6.94/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.94/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.50  
% 6.94/1.50  ------ Combination Options
% 6.94/1.50  
% 6.94/1.50  --comb_res_mult                         3
% 6.94/1.50  --comb_sup_mult                         2
% 6.94/1.50  --comb_inst_mult                        10
% 6.94/1.50  
% 6.94/1.50  ------ Debug Options
% 6.94/1.50  
% 6.94/1.50  --dbg_backtrace                         false
% 6.94/1.50  --dbg_dump_prop_clauses                 false
% 6.94/1.50  --dbg_dump_prop_clauses_file            -
% 6.94/1.50  --dbg_out_stat                          false
% 6.94/1.50  ------ Parsing...
% 6.94/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.94/1.50  
% 6.94/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.94/1.50  
% 6.94/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.94/1.50  
% 6.94/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.94/1.50  ------ Proving...
% 6.94/1.50  ------ Problem Properties 
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  clauses                                 32
% 6.94/1.50  conjectures                             3
% 6.94/1.50  EPR                                     9
% 6.94/1.50  Horn                                    29
% 6.94/1.50  unary                                   9
% 6.94/1.50  binary                                  10
% 6.94/1.50  lits                                    73
% 6.94/1.50  lits eq                                 32
% 6.94/1.50  fd_pure                                 0
% 6.94/1.50  fd_pseudo                               0
% 6.94/1.50  fd_cond                                 6
% 6.94/1.50  fd_pseudo_cond                          1
% 6.94/1.50  AC symbols                              0
% 6.94/1.50  
% 6.94/1.50  ------ Schedule dynamic 5 is on 
% 6.94/1.50  
% 6.94/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  ------ 
% 6.94/1.50  Current options:
% 6.94/1.50  ------ 
% 6.94/1.50  
% 6.94/1.50  ------ Input Options
% 6.94/1.50  
% 6.94/1.50  --out_options                           all
% 6.94/1.50  --tptp_safe_out                         true
% 6.94/1.50  --problem_path                          ""
% 6.94/1.50  --include_path                          ""
% 6.94/1.50  --clausifier                            res/vclausify_rel
% 6.94/1.50  --clausifier_options                    --mode clausify
% 6.94/1.50  --stdin                                 false
% 6.94/1.50  --stats_out                             all
% 6.94/1.50  
% 6.94/1.50  ------ General Options
% 6.94/1.50  
% 6.94/1.50  --fof                                   false
% 6.94/1.50  --time_out_real                         305.
% 6.94/1.50  --time_out_virtual                      -1.
% 6.94/1.50  --symbol_type_check                     false
% 6.94/1.50  --clausify_out                          false
% 6.94/1.50  --sig_cnt_out                           false
% 6.94/1.50  --trig_cnt_out                          false
% 6.94/1.50  --trig_cnt_out_tolerance                1.
% 6.94/1.50  --trig_cnt_out_sk_spl                   false
% 6.94/1.50  --abstr_cl_out                          false
% 6.94/1.50  
% 6.94/1.50  ------ Global Options
% 6.94/1.50  
% 6.94/1.50  --schedule                              default
% 6.94/1.50  --add_important_lit                     false
% 6.94/1.50  --prop_solver_per_cl                    1000
% 6.94/1.50  --min_unsat_core                        false
% 6.94/1.50  --soft_assumptions                      false
% 6.94/1.50  --soft_lemma_size                       3
% 6.94/1.50  --prop_impl_unit_size                   0
% 6.94/1.50  --prop_impl_unit                        []
% 6.94/1.50  --share_sel_clauses                     true
% 6.94/1.50  --reset_solvers                         false
% 6.94/1.50  --bc_imp_inh                            [conj_cone]
% 6.94/1.50  --conj_cone_tolerance                   3.
% 6.94/1.50  --extra_neg_conj                        none
% 6.94/1.50  --large_theory_mode                     true
% 6.94/1.50  --prolific_symb_bound                   200
% 6.94/1.50  --lt_threshold                          2000
% 6.94/1.50  --clause_weak_htbl                      true
% 6.94/1.50  --gc_record_bc_elim                     false
% 6.94/1.50  
% 6.94/1.50  ------ Preprocessing Options
% 6.94/1.50  
% 6.94/1.50  --preprocessing_flag                    true
% 6.94/1.50  --time_out_prep_mult                    0.1
% 6.94/1.50  --splitting_mode                        input
% 6.94/1.50  --splitting_grd                         true
% 6.94/1.50  --splitting_cvd                         false
% 6.94/1.50  --splitting_cvd_svl                     false
% 6.94/1.50  --splitting_nvd                         32
% 6.94/1.50  --sub_typing                            true
% 6.94/1.50  --prep_gs_sim                           true
% 6.94/1.50  --prep_unflatten                        true
% 6.94/1.50  --prep_res_sim                          true
% 6.94/1.50  --prep_upred                            true
% 6.94/1.50  --prep_sem_filter                       exhaustive
% 6.94/1.50  --prep_sem_filter_out                   false
% 6.94/1.50  --pred_elim                             true
% 6.94/1.50  --res_sim_input                         true
% 6.94/1.50  --eq_ax_congr_red                       true
% 6.94/1.50  --pure_diseq_elim                       true
% 6.94/1.50  --brand_transform                       false
% 6.94/1.50  --non_eq_to_eq                          false
% 6.94/1.50  --prep_def_merge                        true
% 6.94/1.50  --prep_def_merge_prop_impl              false
% 6.94/1.50  --prep_def_merge_mbd                    true
% 6.94/1.50  --prep_def_merge_tr_red                 false
% 6.94/1.50  --prep_def_merge_tr_cl                  false
% 6.94/1.50  --smt_preprocessing                     true
% 6.94/1.50  --smt_ac_axioms                         fast
% 6.94/1.50  --preprocessed_out                      false
% 6.94/1.50  --preprocessed_stats                    false
% 6.94/1.50  
% 6.94/1.50  ------ Abstraction refinement Options
% 6.94/1.50  
% 6.94/1.50  --abstr_ref                             []
% 6.94/1.50  --abstr_ref_prep                        false
% 6.94/1.50  --abstr_ref_until_sat                   false
% 6.94/1.50  --abstr_ref_sig_restrict                funpre
% 6.94/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.94/1.50  --abstr_ref_under                       []
% 6.94/1.50  
% 6.94/1.50  ------ SAT Options
% 6.94/1.50  
% 6.94/1.50  --sat_mode                              false
% 6.94/1.50  --sat_fm_restart_options                ""
% 6.94/1.50  --sat_gr_def                            false
% 6.94/1.50  --sat_epr_types                         true
% 6.94/1.50  --sat_non_cyclic_types                  false
% 6.94/1.50  --sat_finite_models                     false
% 6.94/1.50  --sat_fm_lemmas                         false
% 6.94/1.50  --sat_fm_prep                           false
% 6.94/1.50  --sat_fm_uc_incr                        true
% 6.94/1.50  --sat_out_model                         small
% 6.94/1.50  --sat_out_clauses                       false
% 6.94/1.50  
% 6.94/1.50  ------ QBF Options
% 6.94/1.50  
% 6.94/1.50  --qbf_mode                              false
% 6.94/1.50  --qbf_elim_univ                         false
% 6.94/1.50  --qbf_dom_inst                          none
% 6.94/1.50  --qbf_dom_pre_inst                      false
% 6.94/1.50  --qbf_sk_in                             false
% 6.94/1.50  --qbf_pred_elim                         true
% 6.94/1.50  --qbf_split                             512
% 6.94/1.50  
% 6.94/1.50  ------ BMC1 Options
% 6.94/1.50  
% 6.94/1.50  --bmc1_incremental                      false
% 6.94/1.50  --bmc1_axioms                           reachable_all
% 6.94/1.50  --bmc1_min_bound                        0
% 6.94/1.50  --bmc1_max_bound                        -1
% 6.94/1.50  --bmc1_max_bound_default                -1
% 6.94/1.50  --bmc1_symbol_reachability              true
% 6.94/1.50  --bmc1_property_lemmas                  false
% 6.94/1.50  --bmc1_k_induction                      false
% 6.94/1.50  --bmc1_non_equiv_states                 false
% 6.94/1.50  --bmc1_deadlock                         false
% 6.94/1.50  --bmc1_ucm                              false
% 6.94/1.50  --bmc1_add_unsat_core                   none
% 6.94/1.50  --bmc1_unsat_core_children              false
% 6.94/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.94/1.50  --bmc1_out_stat                         full
% 6.94/1.50  --bmc1_ground_init                      false
% 6.94/1.50  --bmc1_pre_inst_next_state              false
% 6.94/1.50  --bmc1_pre_inst_state                   false
% 6.94/1.50  --bmc1_pre_inst_reach_state             false
% 6.94/1.50  --bmc1_out_unsat_core                   false
% 6.94/1.50  --bmc1_aig_witness_out                  false
% 6.94/1.50  --bmc1_verbose                          false
% 6.94/1.50  --bmc1_dump_clauses_tptp                false
% 6.94/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.94/1.50  --bmc1_dump_file                        -
% 6.94/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.94/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.94/1.50  --bmc1_ucm_extend_mode                  1
% 6.94/1.50  --bmc1_ucm_init_mode                    2
% 6.94/1.50  --bmc1_ucm_cone_mode                    none
% 6.94/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.94/1.50  --bmc1_ucm_relax_model                  4
% 6.94/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.94/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.94/1.50  --bmc1_ucm_layered_model                none
% 6.94/1.50  --bmc1_ucm_max_lemma_size               10
% 6.94/1.50  
% 6.94/1.50  ------ AIG Options
% 6.94/1.50  
% 6.94/1.50  --aig_mode                              false
% 6.94/1.50  
% 6.94/1.50  ------ Instantiation Options
% 6.94/1.50  
% 6.94/1.50  --instantiation_flag                    true
% 6.94/1.50  --inst_sos_flag                         false
% 6.94/1.50  --inst_sos_phase                        true
% 6.94/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.94/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.94/1.50  --inst_lit_sel_side                     none
% 6.94/1.50  --inst_solver_per_active                1400
% 6.94/1.50  --inst_solver_calls_frac                1.
% 6.94/1.50  --inst_passive_queue_type               priority_queues
% 6.94/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.94/1.50  --inst_passive_queues_freq              [25;2]
% 6.94/1.50  --inst_dismatching                      true
% 6.94/1.50  --inst_eager_unprocessed_to_passive     true
% 6.94/1.50  --inst_prop_sim_given                   true
% 6.94/1.50  --inst_prop_sim_new                     false
% 6.94/1.50  --inst_subs_new                         false
% 6.94/1.50  --inst_eq_res_simp                      false
% 6.94/1.50  --inst_subs_given                       false
% 6.94/1.50  --inst_orphan_elimination               true
% 6.94/1.50  --inst_learning_loop_flag               true
% 6.94/1.50  --inst_learning_start                   3000
% 6.94/1.50  --inst_learning_factor                  2
% 6.94/1.50  --inst_start_prop_sim_after_learn       3
% 6.94/1.50  --inst_sel_renew                        solver
% 6.94/1.50  --inst_lit_activity_flag                true
% 6.94/1.50  --inst_restr_to_given                   false
% 6.94/1.50  --inst_activity_threshold               500
% 6.94/1.50  --inst_out_proof                        true
% 6.94/1.50  
% 6.94/1.50  ------ Resolution Options
% 6.94/1.50  
% 6.94/1.50  --resolution_flag                       false
% 6.94/1.50  --res_lit_sel                           adaptive
% 6.94/1.50  --res_lit_sel_side                      none
% 6.94/1.50  --res_ordering                          kbo
% 6.94/1.50  --res_to_prop_solver                    active
% 6.94/1.50  --res_prop_simpl_new                    false
% 6.94/1.50  --res_prop_simpl_given                  true
% 6.94/1.50  --res_passive_queue_type                priority_queues
% 6.94/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.94/1.50  --res_passive_queues_freq               [15;5]
% 6.94/1.50  --res_forward_subs                      full
% 6.94/1.50  --res_backward_subs                     full
% 6.94/1.50  --res_forward_subs_resolution           true
% 6.94/1.50  --res_backward_subs_resolution          true
% 6.94/1.50  --res_orphan_elimination                true
% 6.94/1.50  --res_time_limit                        2.
% 6.94/1.50  --res_out_proof                         true
% 6.94/1.50  
% 6.94/1.50  ------ Superposition Options
% 6.94/1.50  
% 6.94/1.50  --superposition_flag                    true
% 6.94/1.50  --sup_passive_queue_type                priority_queues
% 6.94/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.94/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.94/1.50  --demod_completeness_check              fast
% 6.94/1.50  --demod_use_ground                      true
% 6.94/1.50  --sup_to_prop_solver                    passive
% 6.94/1.50  --sup_prop_simpl_new                    true
% 6.94/1.50  --sup_prop_simpl_given                  true
% 6.94/1.50  --sup_fun_splitting                     false
% 6.94/1.50  --sup_smt_interval                      50000
% 6.94/1.50  
% 6.94/1.50  ------ Superposition Simplification Setup
% 6.94/1.50  
% 6.94/1.50  --sup_indices_passive                   []
% 6.94/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.94/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.50  --sup_full_bw                           [BwDemod]
% 6.94/1.50  --sup_immed_triv                        [TrivRules]
% 6.94/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.50  --sup_immed_bw_main                     []
% 6.94/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.94/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.50  
% 6.94/1.50  ------ Combination Options
% 6.94/1.50  
% 6.94/1.50  --comb_res_mult                         3
% 6.94/1.50  --comb_sup_mult                         2
% 6.94/1.50  --comb_inst_mult                        10
% 6.94/1.50  
% 6.94/1.50  ------ Debug Options
% 6.94/1.50  
% 6.94/1.50  --dbg_backtrace                         false
% 6.94/1.50  --dbg_dump_prop_clauses                 false
% 6.94/1.50  --dbg_dump_prop_clauses_file            -
% 6.94/1.50  --dbg_out_stat                          false
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  ------ Proving...
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  % SZS status Theorem for theBenchmark.p
% 6.94/1.50  
% 6.94/1.50   Resolution empty clause
% 6.94/1.50  
% 6.94/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.94/1.50  
% 6.94/1.50  fof(f20,axiom,(
% 6.94/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f38,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.94/1.50    inference(ennf_transformation,[],[f20])).
% 6.94/1.50  
% 6.94/1.50  fof(f39,plain,(
% 6.94/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.94/1.50    inference(flattening,[],[f38])).
% 6.94/1.50  
% 6.94/1.50  fof(f50,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.94/1.50    inference(nnf_transformation,[],[f39])).
% 6.94/1.50  
% 6.94/1.50  fof(f79,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f50])).
% 6.94/1.50  
% 6.94/1.50  fof(f21,conjecture,(
% 6.94/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f22,negated_conjecture,(
% 6.94/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.94/1.50    inference(negated_conjecture,[],[f21])).
% 6.94/1.50  
% 6.94/1.50  fof(f40,plain,(
% 6.94/1.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 6.94/1.50    inference(ennf_transformation,[],[f22])).
% 6.94/1.50  
% 6.94/1.50  fof(f41,plain,(
% 6.94/1.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 6.94/1.50    inference(flattening,[],[f40])).
% 6.94/1.50  
% 6.94/1.50  fof(f51,plain,(
% 6.94/1.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 6.94/1.50    introduced(choice_axiom,[])).
% 6.94/1.50  
% 6.94/1.50  fof(f52,plain,(
% 6.94/1.50    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 6.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f51])).
% 6.94/1.50  
% 6.94/1.50  fof(f86,plain,(
% 6.94/1.50    v1_funct_2(sK4,sK1,sK2)),
% 6.94/1.50    inference(cnf_transformation,[],[f52])).
% 6.94/1.50  
% 6.94/1.50  fof(f87,plain,(
% 6.94/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 6.94/1.50    inference(cnf_transformation,[],[f52])).
% 6.94/1.50  
% 6.94/1.50  fof(f17,axiom,(
% 6.94/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f34,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.94/1.50    inference(ennf_transformation,[],[f17])).
% 6.94/1.50  
% 6.94/1.50  fof(f76,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f34])).
% 6.94/1.50  
% 6.94/1.50  fof(f16,axiom,(
% 6.94/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f23,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.94/1.50    inference(pure_predicate_removal,[],[f16])).
% 6.94/1.50  
% 6.94/1.50  fof(f33,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.94/1.50    inference(ennf_transformation,[],[f23])).
% 6.94/1.50  
% 6.94/1.50  fof(f75,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f33])).
% 6.94/1.50  
% 6.94/1.50  fof(f11,axiom,(
% 6.94/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f29,plain,(
% 6.94/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.94/1.50    inference(ennf_transformation,[],[f11])).
% 6.94/1.50  
% 6.94/1.50  fof(f49,plain,(
% 6.94/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.94/1.50    inference(nnf_transformation,[],[f29])).
% 6.94/1.50  
% 6.94/1.50  fof(f68,plain,(
% 6.94/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f49])).
% 6.94/1.50  
% 6.94/1.50  fof(f18,axiom,(
% 6.94/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f35,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.94/1.50    inference(ennf_transformation,[],[f18])).
% 6.94/1.50  
% 6.94/1.50  fof(f77,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f35])).
% 6.94/1.50  
% 6.94/1.50  fof(f88,plain,(
% 6.94/1.50    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 6.94/1.50    inference(cnf_transformation,[],[f52])).
% 6.94/1.50  
% 6.94/1.50  fof(f19,axiom,(
% 6.94/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f36,plain,(
% 6.94/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 6.94/1.50    inference(ennf_transformation,[],[f19])).
% 6.94/1.50  
% 6.94/1.50  fof(f37,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 6.94/1.50    inference(flattening,[],[f36])).
% 6.94/1.50  
% 6.94/1.50  fof(f78,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f37])).
% 6.94/1.50  
% 6.94/1.50  fof(f8,axiom,(
% 6.94/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f48,plain,(
% 6.94/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.94/1.50    inference(nnf_transformation,[],[f8])).
% 6.94/1.50  
% 6.94/1.50  fof(f64,plain,(
% 6.94/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f48])).
% 6.94/1.50  
% 6.94/1.50  fof(f10,axiom,(
% 6.94/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f28,plain,(
% 6.94/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.94/1.50    inference(ennf_transformation,[],[f10])).
% 6.94/1.50  
% 6.94/1.50  fof(f67,plain,(
% 6.94/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f28])).
% 6.94/1.50  
% 6.94/1.50  fof(f65,plain,(
% 6.94/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f48])).
% 6.94/1.50  
% 6.94/1.50  fof(f13,axiom,(
% 6.94/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f71,plain,(
% 6.94/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f13])).
% 6.94/1.50  
% 6.94/1.50  fof(f81,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f50])).
% 6.94/1.50  
% 6.94/1.50  fof(f90,plain,(
% 6.94/1.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 6.94/1.50    inference(cnf_transformation,[],[f52])).
% 6.94/1.50  
% 6.94/1.50  fof(f85,plain,(
% 6.94/1.50    v1_funct_1(sK4)),
% 6.94/1.50    inference(cnf_transformation,[],[f52])).
% 6.94/1.50  
% 6.94/1.50  fof(f89,plain,(
% 6.94/1.50    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 6.94/1.50    inference(cnf_transformation,[],[f52])).
% 6.94/1.50  
% 6.94/1.50  fof(f1,axiom,(
% 6.94/1.50    v1_xboole_0(k1_xboole_0)),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f53,plain,(
% 6.94/1.50    v1_xboole_0(k1_xboole_0)),
% 6.94/1.50    inference(cnf_transformation,[],[f1])).
% 6.94/1.50  
% 6.94/1.50  fof(f4,axiom,(
% 6.94/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f44,plain,(
% 6.94/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.94/1.50    inference(nnf_transformation,[],[f4])).
% 6.94/1.50  
% 6.94/1.50  fof(f45,plain,(
% 6.94/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.94/1.50    inference(flattening,[],[f44])).
% 6.94/1.50  
% 6.94/1.50  fof(f56,plain,(
% 6.94/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.94/1.50    inference(cnf_transformation,[],[f45])).
% 6.94/1.50  
% 6.94/1.50  fof(f92,plain,(
% 6.94/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.94/1.50    inference(equality_resolution,[],[f56])).
% 6.94/1.50  
% 6.94/1.50  fof(f3,axiom,(
% 6.94/1.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f25,plain,(
% 6.94/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 6.94/1.50    inference(ennf_transformation,[],[f3])).
% 6.94/1.50  
% 6.94/1.50  fof(f42,plain,(
% 6.94/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.94/1.50    introduced(choice_axiom,[])).
% 6.94/1.50  
% 6.94/1.50  fof(f43,plain,(
% 6.94/1.50    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 6.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f42])).
% 6.94/1.50  
% 6.94/1.50  fof(f55,plain,(
% 6.94/1.50    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 6.94/1.50    inference(cnf_transformation,[],[f43])).
% 6.94/1.50  
% 6.94/1.50  fof(f9,axiom,(
% 6.94/1.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f27,plain,(
% 6.94/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 6.94/1.50    inference(ennf_transformation,[],[f9])).
% 6.94/1.50  
% 6.94/1.50  fof(f66,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f27])).
% 6.94/1.50  
% 6.94/1.50  fof(f15,axiom,(
% 6.94/1.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f31,plain,(
% 6.94/1.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 6.94/1.50    inference(ennf_transformation,[],[f15])).
% 6.94/1.50  
% 6.94/1.50  fof(f32,plain,(
% 6.94/1.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 6.94/1.50    inference(flattening,[],[f31])).
% 6.94/1.50  
% 6.94/1.50  fof(f74,plain,(
% 6.94/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f32])).
% 6.94/1.50  
% 6.94/1.50  fof(f7,axiom,(
% 6.94/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f46,plain,(
% 6.94/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.94/1.50    inference(nnf_transformation,[],[f7])).
% 6.94/1.50  
% 6.94/1.50  fof(f47,plain,(
% 6.94/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.94/1.50    inference(flattening,[],[f46])).
% 6.94/1.50  
% 6.94/1.50  fof(f63,plain,(
% 6.94/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 6.94/1.50    inference(cnf_transformation,[],[f47])).
% 6.94/1.50  
% 6.94/1.50  fof(f93,plain,(
% 6.94/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.94/1.50    inference(equality_resolution,[],[f63])).
% 6.94/1.50  
% 6.94/1.50  fof(f62,plain,(
% 6.94/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 6.94/1.50    inference(cnf_transformation,[],[f47])).
% 6.94/1.50  
% 6.94/1.50  fof(f94,plain,(
% 6.94/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.94/1.50    inference(equality_resolution,[],[f62])).
% 6.94/1.50  
% 6.94/1.50  fof(f5,axiom,(
% 6.94/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f59,plain,(
% 6.94/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f5])).
% 6.94/1.50  
% 6.94/1.50  fof(f61,plain,(
% 6.94/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f47])).
% 6.94/1.50  
% 6.94/1.50  fof(f83,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f50])).
% 6.94/1.50  
% 6.94/1.50  fof(f97,plain,(
% 6.94/1.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.94/1.50    inference(equality_resolution,[],[f83])).
% 6.94/1.50  
% 6.94/1.50  fof(f6,axiom,(
% 6.94/1.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 6.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.50  
% 6.94/1.50  fof(f26,plain,(
% 6.94/1.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 6.94/1.50    inference(ennf_transformation,[],[f6])).
% 6.94/1.50  
% 6.94/1.50  fof(f60,plain,(
% 6.94/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f26])).
% 6.94/1.50  
% 6.94/1.50  fof(f73,plain,(
% 6.94/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f32])).
% 6.94/1.50  
% 6.94/1.50  fof(f58,plain,(
% 6.94/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.94/1.50    inference(cnf_transformation,[],[f45])).
% 6.94/1.50  
% 6.94/1.50  fof(f80,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f50])).
% 6.94/1.50  
% 6.94/1.50  fof(f99,plain,(
% 6.94/1.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.94/1.50    inference(equality_resolution,[],[f80])).
% 6.94/1.50  
% 6.94/1.50  fof(f82,plain,(
% 6.94/1.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.94/1.50    inference(cnf_transformation,[],[f50])).
% 6.94/1.50  
% 6.94/1.50  fof(f98,plain,(
% 6.94/1.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.94/1.50    inference(equality_resolution,[],[f82])).
% 6.94/1.50  
% 6.94/1.50  cnf(c_31,plain,
% 6.94/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.94/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.50      | k1_relset_1(X1,X2,X0) = X1
% 6.94/1.50      | k1_xboole_0 = X2 ),
% 6.94/1.50      inference(cnf_transformation,[],[f79]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_36,negated_conjecture,
% 6.94/1.50      ( v1_funct_2(sK4,sK1,sK2) ),
% 6.94/1.50      inference(cnf_transformation,[],[f86]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_581,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.50      | k1_relset_1(X1,X2,X0) = X1
% 6.94/1.50      | sK2 != X2
% 6.94/1.50      | sK1 != X1
% 6.94/1.50      | sK4 != X0
% 6.94/1.50      | k1_xboole_0 = X2 ),
% 6.94/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_582,plain,
% 6.94/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 6.94/1.50      | k1_relset_1(sK1,sK2,sK4) = sK1
% 6.94/1.50      | k1_xboole_0 = sK2 ),
% 6.94/1.50      inference(unflattening,[status(thm)],[c_581]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_35,negated_conjecture,
% 6.94/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 6.94/1.50      inference(cnf_transformation,[],[f87]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_584,plain,
% 6.94/1.50      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 6.94/1.50      inference(global_propositional_subsumption,[status(thm)],[c_582,c_35]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1515,plain,
% 6.94/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_23,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.94/1.50      inference(cnf_transformation,[],[f76]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1519,plain,
% 6.94/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.94/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_3857,plain,
% 6.94/1.50      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_1515,c_1519]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_4041,plain,
% 6.94/1.50      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_584,c_3857]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_22,plain,
% 6.94/1.50      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.94/1.50      inference(cnf_transformation,[],[f75]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_16,plain,
% 6.94/1.50      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 6.94/1.50      inference(cnf_transformation,[],[f68]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_469,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 6.94/1.50      | ~ v1_relat_1(X0) ),
% 6.94/1.50      inference(resolution,[status(thm)],[c_22,c_16]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1512,plain,
% 6.94/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.94/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 6.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1849,plain,
% 6.94/1.50      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
% 6.94/1.50      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_1515,c_1512]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_24,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.94/1.50      inference(cnf_transformation,[],[f77]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1518,plain,
% 6.94/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.94/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_3590,plain,
% 6.94/1.50      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_1515,c_1518]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_34,negated_conjecture,
% 6.94/1.50      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 6.94/1.50      inference(cnf_transformation,[],[f88]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1516,plain,
% 6.94/1.50      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_3895,plain,
% 6.94/1.50      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 6.94/1.50      inference(demodulation,[status(thm)],[c_3590,c_1516]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_25,plain,
% 6.94/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.50      | ~ r1_tarski(k2_relat_1(X0),X2)
% 6.94/1.50      | ~ r1_tarski(k1_relat_1(X0),X1)
% 6.94/1.50      | ~ v1_relat_1(X0) ),
% 6.94/1.50      inference(cnf_transformation,[],[f78]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1517,plain,
% 6.94/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 6.94/1.50      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 6.94/1.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 6.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_3856,plain,
% 6.94/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.94/1.50      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 6.94/1.50      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 6.94/1.50      | v1_relat_1(X2) != iProver_top ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_1517,c_1519]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_27738,plain,
% 6.94/1.50      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 6.94/1.50      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 6.94/1.50      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_3895,c_3856]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_12,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.94/1.50      inference(cnf_transformation,[],[f64]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1525,plain,
% 6.94/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.94/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_2988,plain,
% 6.94/1.50      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_1515,c_1525]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_14,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.94/1.50      inference(cnf_transformation,[],[f67]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_11,plain,
% 6.94/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.94/1.50      inference(cnf_transformation,[],[f65]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_273,plain,
% 6.94/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.94/1.50      inference(prop_impl,[status(thm)],[c_11]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_274,plain,
% 6.94/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.94/1.50      inference(renaming,[status(thm)],[c_273]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_336,plain,
% 6.94/1.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.94/1.50      inference(bin_hyper_res,[status(thm)],[c_14,c_274]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1514,plain,
% 6.94/1.50      ( r1_tarski(X0,X1) != iProver_top
% 6.94/1.50      | v1_relat_1(X1) != iProver_top
% 6.94/1.50      | v1_relat_1(X0) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_3232,plain,
% 6.94/1.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 6.94/1.50      | v1_relat_1(sK4) = iProver_top ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_2988,c_1514]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_18,plain,
% 6.94/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.94/1.50      inference(cnf_transformation,[],[f71]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1523,plain,
% 6.94/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_3367,plain,
% 6.94/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 6.94/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_3232,c_1523]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_29354,plain,
% 6.94/1.50      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 6.94/1.50      | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
% 6.94/1.50      inference(global_propositional_subsumption,
% 6.94/1.50                [status(thm)],
% 6.94/1.50                [c_27738,c_3367]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_29355,plain,
% 6.94/1.50      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 6.94/1.50      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 6.94/1.50      inference(renaming,[status(thm)],[c_29354]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_29365,plain,
% 6.94/1.50      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
% 6.94/1.50      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.50      inference(superposition,[status(thm)],[c_1849,c_29355]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_29515,plain,
% 6.94/1.50      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 6.94/1.50      inference(global_propositional_subsumption,
% 6.94/1.50                [status(thm)],
% 6.94/1.50                [c_29365,c_3367]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_29,plain,
% 6.94/1.50      ( v1_funct_2(X0,X1,X2)
% 6.94/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.50      | k1_relset_1(X1,X2,X0) != X1
% 6.94/1.50      | k1_xboole_0 = X2 ),
% 6.94/1.50      inference(cnf_transformation,[],[f81]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_32,negated_conjecture,
% 6.94/1.50      ( ~ v1_funct_2(sK4,sK1,sK3)
% 6.94/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 6.94/1.50      | ~ v1_funct_1(sK4) ),
% 6.94/1.50      inference(cnf_transformation,[],[f90]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_37,negated_conjecture,
% 6.94/1.50      ( v1_funct_1(sK4) ),
% 6.94/1.50      inference(cnf_transformation,[],[f85]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_195,plain,
% 6.94/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 6.94/1.51      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 6.94/1.51      inference(global_propositional_subsumption,[status(thm)],[c_32,c_37]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_196,negated_conjecture,
% 6.94/1.51      ( ~ v1_funct_2(sK4,sK1,sK3)
% 6.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_195]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_568,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 6.94/1.51      | k1_relset_1(X1,X2,X0) != X1
% 6.94/1.51      | sK3 != X2
% 6.94/1.51      | sK1 != X1
% 6.94/1.51      | sK4 != X0
% 6.94/1.51      | k1_xboole_0 = X2 ),
% 6.94/1.51      inference(resolution_lifted,[status(thm)],[c_29,c_196]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_569,plain,
% 6.94/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 6.94/1.51      | k1_relset_1(sK1,sK3,sK4) != sK1
% 6.94/1.51      | k1_xboole_0 = sK3 ),
% 6.94/1.51      inference(unflattening,[status(thm)],[c_568]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1507,plain,
% 6.94/1.51      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 6.94/1.51      | k1_xboole_0 = sK3
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29518,plain,
% 6.94/1.51      ( k1_relat_1(sK4) != sK1
% 6.94/1.51      | sK3 = k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29515,c_1507]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2184,plain,
% 6.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 6.94/1.51      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 6.94/1.51      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 6.94/1.51      | ~ v1_relat_1(sK4) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_25]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2185,plain,
% 6.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 6.94/1.51      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 6.94/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2184]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29521,plain,
% 6.94/1.51      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) != sK1 ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_29518,c_1849,c_2185,c_3367,c_3895]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29522,plain,
% 6.94/1.51      ( k1_relat_1(sK4) != sK1 | sK3 = k1_xboole_0 ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_29521]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29525,plain,
% 6.94/1.51      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_4041,c_29522]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_33,negated_conjecture,
% 6.94/1.51      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 6.94/1.51      inference(cnf_transformation,[],[f89]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29702,plain,
% 6.94/1.51      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_29525,c_33]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_0,plain,
% 6.94/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 6.94/1.51      inference(cnf_transformation,[],[f53]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_881,plain,( X0 = X0 ),theory(equality) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2098,plain,
% 6.94/1.51      ( sK4 = sK4 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_881]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f92]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2731,plain,
% 6.94/1.51      ( r1_tarski(sK4,sK4) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2734,plain,
% 6.94/1.51      ( r1_tarski(sK4,sK4) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3368,plain,
% 6.94/1.51      ( v1_relat_1(sK4) ),
% 6.94/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3367]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2,plain,
% 6.94/1.51      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f55]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_13,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.51      | ~ r2_hidden(X2,X0)
% 6.94/1.51      | ~ v1_xboole_0(X1) ),
% 6.94/1.51      inference(cnf_transformation,[],[f66]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_335,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 6.94/1.51      inference(bin_hyper_res,[status(thm)],[c_13,c_274]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_452,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,X1)
% 6.94/1.51      | ~ v1_xboole_0(X1)
% 6.94/1.51      | X0 != X2
% 6.94/1.51      | sK0(X2) != X3
% 6.94/1.51      | k1_xboole_0 = X2 ),
% 6.94/1.51      inference(resolution_lifted,[status(thm)],[c_2,c_335]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_453,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | k1_xboole_0 = X0 ),
% 6.94/1.51      inference(unflattening,[status(thm)],[c_452]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1513,plain,
% 6.94/1.51      ( k1_xboole_0 = X0
% 6.94/1.51      | r1_tarski(X0,X1) != iProver_top
% 6.94/1.51      | v1_xboole_0(X1) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2349,plain,
% 6.94/1.51      ( k2_relset_1(sK1,sK2,sK4) = k1_xboole_0
% 6.94/1.51      | v1_xboole_0(sK3) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_1516,c_1513]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3894,plain,
% 6.94/1.51      ( k2_relat_1(sK4) = k1_xboole_0 | v1_xboole_0(sK3) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_3590,c_2349]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3907,plain,
% 6.94/1.51      ( ~ v1_xboole_0(sK3) | k2_relat_1(sK4) = k1_xboole_0 ),
% 6.94/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3894]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_883,plain,
% 6.94/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.94/1.51      theory(equality) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_4513,plain,
% 6.94/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_883]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_4515,plain,
% 6.94/1.51      ( v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_4513]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_20,plain,
% 6.94/1.51      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f74]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5497,plain,
% 6.94/1.51      ( ~ v1_relat_1(sK4)
% 6.94/1.51      | k2_relat_1(sK4) != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 = sK4 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_884,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.94/1.51      theory(equality) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2551,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_884]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5133,plain,
% 6.94/1.51      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) | X1 != X0 | sK4 != sK4 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_2551]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_10467,plain,
% 6.94/1.51      ( r1_tarski(sK4,X0) | ~ r1_tarski(sK4,sK4) | X0 != sK4 | sK4 != sK4 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_5133]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_10468,plain,
% 6.94/1.51      ( X0 != sK4
% 6.94/1.51      | sK4 != sK4
% 6.94/1.51      | r1_tarski(sK4,X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK4,sK4) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_10467]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_10470,plain,
% 6.94/1.51      ( sK4 != sK4
% 6.94/1.51      | k1_xboole_0 != sK4
% 6.94/1.51      | r1_tarski(sK4,sK4) != iProver_top
% 6.94/1.51      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_10468]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1526,plain,
% 6.94/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 6.94/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_8,plain,
% 6.94/1.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f93]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1852,plain,
% 6.94/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_8,c_1512]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_4642,plain,
% 6.94/1.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_1526,c_1852]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2994,plain,
% 6.94/1.51      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_1526,c_1512]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_9914,plain,
% 6.94/1.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_4642,c_2994]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_9,plain,
% 6.94/1.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f94]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5212,plain,
% 6.94/1.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_9,c_2994]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5279,plain,
% 6.94/1.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | v1_relat_1(k1_relat_1(X0)) = iProver_top
% 6.94/1.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_5212,c_1514]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_82,plain,
% 6.94/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1752,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 6.94/1.51      | v1_relat_1(X0)
% 6.94/1.51      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_336]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1870,plain,
% 6.94/1.51      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
% 6.94/1.51      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 6.94/1.51      | v1_relat_1(k1_xboole_0) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_1752]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1872,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
% 6.94/1.51      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 6.94/1.51      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_1870]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,X0) ),
% 6.94/1.51      inference(cnf_transformation,[],[f59]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1871,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1874,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_1871]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_12755,plain,
% 6.94/1.51      ( v1_relat_1(k1_relat_1(X0)) = iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_5279,c_82,c_1872,c_1874]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_12756,plain,
% 6.94/1.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_12755]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_22404,plain,
% 6.94/1.51      ( v1_relat_1(X0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
% 6.94/1.51      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_9914,c_12756]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_22405,plain,
% 6.94/1.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_22404]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_22414,plain,
% 6.94/1.51      ( sK2 = k1_xboole_0
% 6.94/1.51      | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_4041,c_22405]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5277,plain,
% 6.94/1.51      ( sK2 = k1_xboole_0
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 6.94/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_4041,c_5212]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_10,plain,
% 6.94/1.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 = X0
% 6.94/1.51      | k1_xboole_0 = X1 ),
% 6.94/1.51      inference(cnf_transformation,[],[f61]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_104,plain,
% 6.94/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 = k1_xboole_0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_105,plain,
% 6.94/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_109,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_111,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_109]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1826,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,X1)
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0)
% 6.94/1.51      | sK1 != X0
% 6.94/1.51      | k1_xboole_0 != X1 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_884]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1827,plain,
% 6.94/1.51      ( sK1 != X0
% 6.94/1.51      | k1_xboole_0 != X1
% 6.94/1.51      | r1_tarski(X0,X1) != iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_1826]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1829,plain,
% 6.94/1.51      ( sK1 != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 != k1_xboole_0
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 6.94/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_1827]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_27,plain,
% 6.94/1.51      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 6.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.94/1.51      | k1_xboole_0 = X1
% 6.94/1.51      | k1_xboole_0 = X0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f97]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_519,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.94/1.51      | sK2 != k1_xboole_0
% 6.94/1.51      | sK1 != X1
% 6.94/1.51      | sK4 != X0
% 6.94/1.51      | k1_xboole_0 = X0
% 6.94/1.51      | k1_xboole_0 = X1 ),
% 6.94/1.51      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_520,plain,
% 6.94/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 6.94/1.51      | sK2 != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 = sK1
% 6.94/1.51      | k1_xboole_0 = sK4 ),
% 6.94/1.51      inference(unflattening,[status(thm)],[c_519]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1510,plain,
% 6.94/1.51      ( sK2 != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 = sK1
% 6.94/1.51      | k1_xboole_0 = sK4
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1640,plain,
% 6.94/1.51      ( sK2 != k1_xboole_0
% 6.94/1.51      | sK1 = k1_xboole_0
% 6.94/1.51      | sK4 = k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_1510,c_8]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_882,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1775,plain,
% 6.94/1.51      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_882]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1834,plain,
% 6.94/1.51      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_1775]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1835,plain,
% 6.94/1.51      ( sK1 = sK1 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_881]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2053,plain,
% 6.94/1.51      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_882]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2054,plain,
% 6.94/1.51      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_2053]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2180,plain,
% 6.94/1.51      ( sK2 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_1640,c_33,c_104,c_105,c_1834,c_1835,c_2054]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5750,plain,
% 6.94/1.51      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_5277,c_104,c_105,c_111,c_1829,c_2180,c_3367]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5751,plain,
% 6.94/1.51      ( r1_tarski(sK1,k1_xboole_0) = iProver_top
% 6.94/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_5750]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3553,plain,
% 6.94/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.94/1.51      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_9,c_1517]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5578,plain,
% 6.94/1.51      ( sK2 = k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.94/1.51      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_4041,c_3553]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_101,plain,
% 6.94/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 6.94/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_103,plain,
% 6.94/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.94/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_101]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_886,plain,
% 6.94/1.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 6.94/1.51      theory(equality) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_895,plain,
% 6.94/1.51      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 6.94/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_886]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_7,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2015,plain,
% 6.94/1.51      ( ~ r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2019,plain,
% 6.94/1.51      ( k1_xboole_0 = sK1 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2350,plain,
% 6.94/1.51      ( k1_relat_1(sK4) = k1_xboole_0
% 6.94/1.51      | v1_relat_1(sK4) != iProver_top
% 6.94/1.51      | v1_xboole_0(sK1) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_1849,c_1513]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2369,plain,
% 6.94/1.51      ( ~ v1_relat_1(sK4)
% 6.94/1.51      | ~ v1_xboole_0(sK1)
% 6.94/1.51      | k1_relat_1(sK4) = k1_xboole_0 ),
% 6.94/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_2350]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2663,plain,
% 6.94/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_883]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2665,plain,
% 6.94/1.51      ( v1_xboole_0(sK1) | ~ v1_xboole_0(k1_xboole_0) | sK1 != k1_xboole_0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_2663]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2103,plain,
% 6.94/1.51      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_882]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2825,plain,
% 6.94/1.51      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_2103]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2826,plain,
% 6.94/1.51      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_2825]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_887,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.94/1.51      theory(equality) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1795,plain,
% 6.94/1.51      ( m1_subset_1(X0,X1)
% 6.94/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 6.94/1.51      | X0 != X2
% 6.94/1.51      | X1 != k1_zfmisc_1(X3) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_887]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_2004,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.51      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 6.94/1.51      | X2 != X0
% 6.94/1.51      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_1795]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3778,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X2))
% 6.94/1.51      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
% 6.94/1.51      | sK4 != X0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_2004]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3779,plain,
% 6.94/1.51      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 6.94/1.51      | sK4 != X2
% 6.94/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_3778]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3781,plain,
% 6.94/1.51      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 6.94/1.51      | sK4 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.94/1.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_3779]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_21,plain,
% 6.94/1.51      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f73]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5496,plain,
% 6.94/1.51      ( ~ v1_relat_1(sK4)
% 6.94/1.51      | k1_relat_1(sK4) != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 = sK4 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5506,plain,
% 6.94/1.51      ( k1_relat_1(sK4) != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 = sK4
% 6.94/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_5496]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5903,plain,
% 6.94/1.51      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_5578,c_103,c_104,c_105,c_111,c_0,c_895,c_1834,c_1835,
% 6.94/1.51                 c_2019,c_2098,c_2369,c_2665,c_2826,c_3367,c_3368,c_3781,
% 6.94/1.51                 c_5506]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5904,plain,
% 6.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_5903]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_5910,plain,
% 6.94/1.51      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_5904,c_1852]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6698,plain,
% 6.94/1.51      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 6.94/1.51      inference(global_propositional_subsumption,[status(thm)],[c_5910,c_3367]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6699,plain,
% 6.94/1.51      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_6698]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6711,plain,
% 6.94/1.51      ( r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_6699,c_2994]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6708,plain,
% 6.94/1.51      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | v1_relat_1(k1_relat_1(sK4)) = iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_6699,c_1514]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6761,plain,
% 6.94/1.51      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(k1_relat_1(sK4)) = iProver_top
% 6.94/1.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_6708]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_7676,plain,
% 6.94/1.51      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) = iProver_top ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_6711,c_82,c_1872,c_1874,c_6761]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_7677,plain,
% 6.94/1.51      ( r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_7676]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_7684,plain,
% 6.94/1.51      ( sK2 = k1_xboole_0
% 6.94/1.51      | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_4041,c_7677]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_23244,plain,
% 6.94/1.51      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
% 6.94/1.51      | sK2 = k1_xboole_0 ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_22414,c_104,c_105,c_111,c_1829,c_2180,c_3367,c_5277,c_7684]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_23245,plain,
% 6.94/1.51      ( sK2 = k1_xboole_0
% 6.94/1.51      | r1_tarski(k1_relat_1(sK1),X0) = iProver_top
% 6.94/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_23244]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1529,plain,
% 6.94/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3554,plain,
% 6.94/1.51      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 6.94/1.51      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_1517,c_1525]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6308,plain,
% 6.94/1.51      ( k1_xboole_0 = X0
% 6.94/1.51      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),X2) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | v1_xboole_0(k2_zfmisc_1(X2,X1)) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_3554,c_1513]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_16532,plain,
% 6.94/1.51      ( k1_xboole_0 = X0
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | v1_xboole_0(k2_zfmisc_1(X1,k2_relat_1(X0))) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_1529,c_6308]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_20466,plain,
% 6.94/1.51      ( k1_xboole_0 = X0
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top
% 6.94/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_9,c_16532]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_121,plain,
% 6.94/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_21451,plain,
% 6.94/1.51      ( v1_relat_1(X0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 6.94/1.51      | k1_xboole_0 = X0 ),
% 6.94/1.51      inference(global_propositional_subsumption,[status(thm)],[c_20466,c_121]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_21452,plain,
% 6.94/1.51      ( k1_xboole_0 = X0
% 6.94/1.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_21451]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_23268,plain,
% 6.94/1.51      ( sK2 = k1_xboole_0
% 6.94/1.51      | sK1 = k1_xboole_0
% 6.94/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 6.94/1.51      | v1_relat_1(sK1) != iProver_top ),
% 6.94/1.51      inference(superposition,[status(thm)],[c_23245,c_21452]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_3,plain,
% 6.94/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 6.94/1.51      inference(cnf_transformation,[],[f58]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1764,plain,
% 6.94/1.51      ( ~ r1_tarski(sK1,k1_xboole_0)
% 6.94/1.51      | ~ r1_tarski(k1_xboole_0,sK1)
% 6.94/1.51      | sK1 = k1_xboole_0 ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1765,plain,
% 6.94/1.51      ( sK1 = k1_xboole_0
% 6.94/1.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 6.94/1.51      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_1764]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6954,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,sK1) ),
% 6.94/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_6957,plain,
% 6.94/1.51      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_6954]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_23956,plain,
% 6.94/1.51      ( r1_tarski(sK4,k1_xboole_0) != iProver_top | sK1 = k1_xboole_0 ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_23268,c_104,c_105,c_111,c_1765,c_1829,c_2180,c_3367,
% 6.94/1.51                 c_5277,c_6957]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_23957,plain,
% 6.94/1.51      ( sK1 = k1_xboole_0 | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 6.94/1.51      inference(renaming,[status(thm)],[c_23956]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29743,plain,
% 6.94/1.51      ( sK1 = k1_xboole_0 ),
% 6.94/1.51      inference(global_propositional_subsumption,
% 6.94/1.51                [status(thm)],
% 6.94/1.51                [c_29702,c_0,c_2098,c_2734,c_3368,c_3907,c_4515,c_5497,
% 6.94/1.51                 c_10470,c_23957]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29747,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29743,c_29515]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29877,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29743,c_3857]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_30,plain,
% 6.94/1.51      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 6.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.94/1.51      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f99]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_555,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.94/1.51      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 6.94/1.51      | sK2 != X1
% 6.94/1.51      | sK1 != k1_xboole_0
% 6.94/1.51      | sK4 != X0 ),
% 6.94/1.51      inference(resolution_lifted,[status(thm)],[c_30,c_36]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_556,plain,
% 6.94/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 6.94/1.51      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 6.94/1.51      | sK1 != k1_xboole_0 ),
% 6.94/1.51      inference(unflattening,[status(thm)],[c_555]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1508,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 6.94/1.51      | sK1 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1633,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 6.94/1.51      | sK1 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_1508,c_9]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29888,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 6.94/1.51      | k1_xboole_0 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29743,c_1633]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29905,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(equality_resolution_simp,[status(thm)],[c_29888]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29891,plain,
% 6.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29743,c_1515]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29894,plain,
% 6.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29891,c_9]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29908,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
% 6.94/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_29905,c_29894]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29946,plain,
% 6.94/1.51      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 6.94/1.51      inference(light_normalisation,[status(thm)],[c_29877,c_29908]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_30399,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
% 6.94/1.51      inference(light_normalisation,[status(thm)],[c_29747,c_29946]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_28,plain,
% 6.94/1.51      ( v1_funct_2(X0,k1_xboole_0,X1)
% 6.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.94/1.51      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 6.94/1.51      inference(cnf_transformation,[],[f98]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_539,plain,
% 6.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 6.94/1.51      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 6.94/1.51      | sK3 != X1
% 6.94/1.51      | sK1 != k1_xboole_0
% 6.94/1.51      | sK4 != X0 ),
% 6.94/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_196]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_540,plain,
% 6.94/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 6.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 6.94/1.51      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 6.94/1.51      | sK1 != k1_xboole_0 ),
% 6.94/1.51      inference(unflattening,[status(thm)],[c_539]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1509,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 6.94/1.51      | sK1 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 6.94/1.51      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_1663,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 6.94/1.51      | sK1 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_1509,c_9]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29887,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 6.94/1.51      | k1_xboole_0 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29743,c_1663]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29910,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(equality_resolution_simp,[status(thm)],[c_29887]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29914,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 6.94/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_29910,c_29894]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_29915,plain,
% 6.94/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_29914,c_9]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_30401,plain,
% 6.94/1.51      ( k1_xboole_0 != k1_xboole_0
% 6.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(demodulation,[status(thm)],[c_30399,c_29915]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_30403,plain,
% 6.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.94/1.51      inference(equality_resolution_simp,[status(thm)],[c_30401]) ).
% 6.94/1.51  
% 6.94/1.51  cnf(c_30405,plain,
% 6.94/1.51      ( $false ),
% 6.94/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_30403,c_29894]) ).
% 6.94/1.51  
% 6.94/1.51  
% 6.94/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.94/1.51  
% 6.94/1.51  ------                               Statistics
% 6.94/1.51  
% 6.94/1.51  ------ General
% 6.94/1.51  
% 6.94/1.51  abstr_ref_over_cycles:                  0
% 6.94/1.51  abstr_ref_under_cycles:                 0
% 6.94/1.51  gc_basic_clause_elim:                   0
% 6.94/1.51  forced_gc_time:                         0
% 6.94/1.51  parsing_time:                           0.009
% 6.94/1.51  unif_index_cands_time:                  0.
% 6.94/1.51  unif_index_add_time:                    0.
% 6.94/1.51  orderings_time:                         0.
% 6.94/1.51  out_proof_time:                         0.02
% 6.94/1.51  total_time:                             0.677
% 6.94/1.51  num_of_symbols:                         51
% 6.94/1.51  num_of_terms:                           19091
% 6.94/1.51  
% 6.94/1.51  ------ Preprocessing
% 6.94/1.51  
% 6.94/1.51  num_of_splits:                          0
% 6.94/1.51  num_of_split_atoms:                     0
% 6.94/1.51  num_of_reused_defs:                     0
% 6.94/1.51  num_eq_ax_congr_red:                    9
% 6.94/1.51  num_of_sem_filtered_clauses:            2
% 6.94/1.51  num_of_subtypes:                        0
% 6.94/1.51  monotx_restored_types:                  0
% 6.94/1.51  sat_num_of_epr_types:                   0
% 6.94/1.51  sat_num_of_non_cyclic_types:            0
% 6.94/1.51  sat_guarded_non_collapsed_types:        0
% 6.94/1.51  num_pure_diseq_elim:                    0
% 6.94/1.51  simp_replaced_by:                       0
% 6.94/1.51  res_preprocessed:                       156
% 6.94/1.51  prep_upred:                             0
% 6.94/1.51  prep_unflattend:                        35
% 6.94/1.51  smt_new_axioms:                         0
% 6.94/1.51  pred_elim_cands:                        4
% 6.94/1.51  pred_elim:                              3
% 6.94/1.51  pred_elim_cl:                           4
% 6.94/1.51  pred_elim_cycles:                       5
% 6.94/1.51  merged_defs:                            8
% 6.94/1.51  merged_defs_ncl:                        0
% 6.94/1.51  bin_hyper_res:                          10
% 6.94/1.51  prep_cycles:                            4
% 6.94/1.51  pred_elim_time:                         0.004
% 6.94/1.51  splitting_time:                         0.
% 6.94/1.51  sem_filter_time:                        0.
% 6.94/1.51  monotx_time:                            0.
% 6.94/1.51  subtype_inf_time:                       0.
% 6.94/1.51  
% 6.94/1.51  ------ Problem properties
% 6.94/1.51  
% 6.94/1.51  clauses:                                32
% 6.94/1.51  conjectures:                            3
% 6.94/1.51  epr:                                    9
% 6.94/1.51  horn:                                   29
% 6.94/1.51  ground:                                 11
% 6.94/1.51  unary:                                  9
% 6.94/1.51  binary:                                 10
% 6.94/1.51  lits:                                   73
% 6.94/1.51  lits_eq:                                32
% 6.94/1.51  fd_pure:                                0
% 6.94/1.51  fd_pseudo:                              0
% 6.94/1.51  fd_cond:                                6
% 6.94/1.51  fd_pseudo_cond:                         1
% 6.94/1.51  ac_symbols:                             0
% 6.94/1.51  
% 6.94/1.51  ------ Propositional Solver
% 6.94/1.51  
% 6.94/1.51  prop_solver_calls:                      33
% 6.94/1.51  prop_fast_solver_calls:                 1927
% 6.94/1.51  smt_solver_calls:                       0
% 6.94/1.51  smt_fast_solver_calls:                  0
% 6.94/1.51  prop_num_of_clauses:                    9981
% 6.94/1.51  prop_preprocess_simplified:             19835
% 6.94/1.51  prop_fo_subsumed:                       104
% 6.94/1.51  prop_solver_time:                       0.
% 6.94/1.51  smt_solver_time:                        0.
% 6.94/1.51  smt_fast_solver_time:                   0.
% 6.94/1.51  prop_fast_solver_time:                  0.
% 6.94/1.51  prop_unsat_core_time:                   0.
% 6.94/1.51  
% 6.94/1.51  ------ QBF
% 6.94/1.51  
% 6.94/1.51  qbf_q_res:                              0
% 6.94/1.51  qbf_num_tautologies:                    0
% 6.94/1.51  qbf_prep_cycles:                        0
% 6.94/1.51  
% 6.94/1.51  ------ BMC1
% 6.94/1.51  
% 6.94/1.51  bmc1_current_bound:                     -1
% 6.94/1.51  bmc1_last_solved_bound:                 -1
% 6.94/1.51  bmc1_unsat_core_size:                   -1
% 6.94/1.51  bmc1_unsat_core_parents_size:           -1
% 6.94/1.51  bmc1_merge_next_fun:                    0
% 6.94/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.94/1.51  
% 6.94/1.51  ------ Instantiation
% 6.94/1.51  
% 6.94/1.51  inst_num_of_clauses:                    3008
% 6.94/1.51  inst_num_in_passive:                    1496
% 6.94/1.51  inst_num_in_active:                     1392
% 6.94/1.51  inst_num_in_unprocessed:                121
% 6.94/1.51  inst_num_of_loops:                      1550
% 6.94/1.51  inst_num_of_learning_restarts:          0
% 6.94/1.51  inst_num_moves_active_passive:          153
% 6.94/1.51  inst_lit_activity:                      0
% 6.94/1.51  inst_lit_activity_moves:                0
% 6.94/1.51  inst_num_tautologies:                   0
% 6.94/1.51  inst_num_prop_implied:                  0
% 6.94/1.51  inst_num_existing_simplified:           0
% 6.94/1.51  inst_num_eq_res_simplified:             0
% 6.94/1.51  inst_num_child_elim:                    0
% 6.94/1.51  inst_num_of_dismatching_blockings:      1746
% 6.94/1.51  inst_num_of_non_proper_insts:           4348
% 6.94/1.51  inst_num_of_duplicates:                 0
% 6.94/1.51  inst_inst_num_from_inst_to_res:         0
% 6.94/1.51  inst_dismatching_checking_time:         0.
% 6.94/1.51  
% 6.94/1.51  ------ Resolution
% 6.94/1.51  
% 6.94/1.51  res_num_of_clauses:                     0
% 6.94/1.51  res_num_in_passive:                     0
% 6.94/1.51  res_num_in_active:                      0
% 6.94/1.51  res_num_of_loops:                       160
% 6.94/1.51  res_forward_subset_subsumed:            232
% 6.94/1.51  res_backward_subset_subsumed:           8
% 6.94/1.51  res_forward_subsumed:                   0
% 6.94/1.51  res_backward_subsumed:                  0
% 6.94/1.51  res_forward_subsumption_resolution:     0
% 6.94/1.51  res_backward_subsumption_resolution:    0
% 6.94/1.51  res_clause_to_clause_subsumption:       4599
% 6.94/1.51  res_orphan_elimination:                 0
% 6.94/1.51  res_tautology_del:                      273
% 6.94/1.51  res_num_eq_res_simplified:              1
% 6.94/1.51  res_num_sel_changes:                    0
% 6.94/1.51  res_moves_from_active_to_pass:          0
% 6.94/1.51  
% 6.94/1.51  ------ Superposition
% 6.94/1.51  
% 6.94/1.51  sup_time_total:                         0.
% 6.94/1.51  sup_time_generating:                    0.
% 6.94/1.51  sup_time_sim_full:                      0.
% 6.94/1.51  sup_time_sim_immed:                     0.
% 6.94/1.51  
% 6.94/1.51  sup_num_of_clauses:                     335
% 6.94/1.51  sup_num_in_active:                      146
% 6.94/1.51  sup_num_in_passive:                     189
% 6.94/1.51  sup_num_of_loops:                       309
% 6.94/1.51  sup_fw_superposition:                   781
% 6.94/1.51  sup_bw_superposition:                   281
% 6.94/1.51  sup_immediate_simplified:               375
% 6.94/1.51  sup_given_eliminated:                   5
% 6.94/1.51  comparisons_done:                       0
% 6.94/1.51  comparisons_avoided:                    168
% 6.94/1.51  
% 6.94/1.51  ------ Simplifications
% 6.94/1.51  
% 6.94/1.51  
% 6.94/1.51  sim_fw_subset_subsumed:                 101
% 6.94/1.51  sim_bw_subset_subsumed:                 20
% 6.94/1.51  sim_fw_subsumed:                        145
% 6.94/1.51  sim_bw_subsumed:                        47
% 6.94/1.51  sim_fw_subsumption_res:                 23
% 6.94/1.51  sim_bw_subsumption_res:                 0
% 6.94/1.51  sim_tautology_del:                      19
% 6.94/1.51  sim_eq_tautology_del:                   156
% 6.94/1.51  sim_eq_res_simp:                        4
% 6.94/1.51  sim_fw_demodulated:                     100
% 6.94/1.51  sim_bw_demodulated:                     155
% 6.94/1.51  sim_light_normalised:                   265
% 6.94/1.51  sim_joinable_taut:                      0
% 6.94/1.51  sim_joinable_simp:                      0
% 6.94/1.51  sim_ac_normalised:                      0
% 6.94/1.51  sim_smt_subsumption:                    0
% 6.94/1.51  
%------------------------------------------------------------------------------
