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
% DateTime   : Thu Dec  3 12:00:35 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  429 (12444 expanded)
%              Number of clauses        :  345 (5257 expanded)
%              Number of leaves         :   28 (2211 expanded)
%              Depth                    :   33
%              Number of atoms          : 1292 (54084 expanded)
%              Number of equality atoms :  861 (19257 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f47])).

fof(f83,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK0(X0,X1),X0,X1)
        & v1_funct_1(sK0(X0,X1))
        & v4_relat_1(sK0(X0,X1),X0)
        & v1_relat_1(sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK0(X0,X1),X0,X1)
      & v1_funct_1(sK0(X0,X1))
      & v4_relat_1(sK0(X0,X1),X0)
      & v1_relat_1(sK0(X0,X1))
      & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f45])).

fof(f81,plain,(
    ! [X0,X1] : v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f77,plain,(
    ! [X0,X1] : m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_653,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_655,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_36])).

cnf(c_1721,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1728,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4180,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1721,c_1728])).

cnf(c_4440,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_655,c_4180])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1729,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3069,plain,
    ( v4_relat_1(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_1729])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1734,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_268,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_331,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_269])).

cnf(c_1720,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_4962,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1720])).

cnf(c_17153,plain,
    ( v1_relat_1(k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_4962])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2690,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_1736])).

cnf(c_3295,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_1720])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1733,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3808,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3295,c_1733])).

cnf(c_17497,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17153,c_3808])).

cnf(c_17498,plain,
    ( v1_relat_1(k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17497])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1739,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1727,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4053,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_1727])).

cnf(c_33697,plain,
    ( k2_relset_1(X0,k2_relat_1(X1),X1) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_4053])).

cnf(c_33833,plain,
    ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_33697])).

cnf(c_33922,plain,
    ( k2_relset_1(k1_relat_1(k1_relat_1(sK4)),k2_relat_1(k1_relat_1(sK4)),k1_relat_1(sK4)) = k2_relat_1(k1_relat_1(sK4))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17498,c_33833])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_99,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_98,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_100,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_114,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_115,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_195,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_38])).

cnf(c_196,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_196])).

cnf(c_640,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_1980,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_1982,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_1981,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_1983,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_2029,plain,
    ( v4_relat_1(sK4,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2030,plain,
    ( v4_relat_1(sK4,sK1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

cnf(c_2076,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2128,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2132,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_2131,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_2133,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_37])).

cnf(c_568,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_1718,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1864,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1718,c_4])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1053,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2046,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_2169,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_1052,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2170,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_2276,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_2277,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2276])).

cnf(c_2358,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1864,c_34,c_114,c_115,c_2169,c_2170,c_2277])).

cnf(c_2423,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2281,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_2712,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2281])).

cnf(c_2713,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2709,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2947,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    | ~ r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
    | sK3 = k2_relset_1(sK1,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2709])).

cnf(c_3345,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1721,c_1727])).

cnf(c_1722,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3697,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3345,c_1722])).

cnf(c_3698,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3697])).

cnf(c_3809,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3808])).

cnf(c_2373,plain,
    ( ~ v4_relat_1(X0,sK1)
    | r1_tarski(k1_relat_1(X0),sK1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4281,plain,
    ( ~ v4_relat_1(sK4,sK1)
    | r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2373])).

cnf(c_4282,plain,
    ( v4_relat_1(sK4,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4281])).

cnf(c_4960,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_1734])).

cnf(c_4987,plain,
    ( ~ v4_relat_1(sK4,X0)
    | r1_tarski(sK1,X0)
    | ~ v1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4960])).

cnf(c_4989,plain,
    ( ~ v4_relat_1(sK4,k1_xboole_0)
    | r1_tarski(sK1,k1_xboole_0)
    | ~ v1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4987])).

cnf(c_5217,plain,
    ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_6317,plain,
    ( ~ r1_tarski(sK1,X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_6324,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | v1_relat_1(sK1)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6317])).

cnf(c_1058,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6339,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_6340,plain,
    ( sK1 != X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6339])).

cnf(c_6342,plain,
    ( sK1 != k1_xboole_0
    | v1_relat_1(sK1) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6340])).

cnf(c_1054,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4837,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
    | k2_relset_1(sK1,sK2,sK4) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_8125,plain,
    ( ~ r1_tarski(X0,k2_relset_1(sK1,sK2,sK4))
    | r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
    | k2_relset_1(sK1,sK2,sK4) != k2_relset_1(sK1,sK2,sK4)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_4837])).

cnf(c_8128,plain,
    ( r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
    | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK4))
    | k2_relset_1(sK1,sK2,sK4) != k2_relset_1(sK1,sK2,sK4)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8125])).

cnf(c_8126,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relset_1(sK1,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1735,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5085,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_1735])).

cnf(c_5297,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | v4_relat_1(sK4,X0) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4960,c_3808])).

cnf(c_5298,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5297])).

cnf(c_8302,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5085,c_5298])).

cnf(c_4909,plain,
    ( k1_relset_1(sK1,sK3,sK4) != X0
    | k1_relset_1(sK1,sK3,sK4) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_8048,plain,
    ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(X0)
    | k1_relset_1(sK1,sK3,sK4) = sK1
    | sK1 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_4909])).

cnf(c_9486,plain,
    ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
    | k1_relset_1(sK1,sK3,sK4) = sK1
    | sK1 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8048])).

cnf(c_9487,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_9827,plain,
    ( r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2647,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_3030,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2647])).

cnf(c_10834,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_10835,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8479,plain,
    ( r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8302,c_3808])).

cnf(c_8480,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8479])).

cnf(c_5088,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_1735])).

cnf(c_5308,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | v4_relat_1(sK4,X0) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5088,c_3808])).

cnf(c_5309,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5308])).

cnf(c_8488,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8480,c_5309])).

cnf(c_4296,plain,
    ( v4_relat_1(sK4,X0)
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5480,plain,
    ( v4_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4296])).

cnf(c_5482,plain,
    ( v4_relat_1(sK4,k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5480])).

cnf(c_5481,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5484,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5481])).

cnf(c_8502,plain,
    ( v4_relat_1(sK4,k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8488,c_3808,c_5482,c_5484])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1730,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8508,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8502,c_1730])).

cnf(c_8606,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8508,c_3808])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1732,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3810,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3808,c_1732])).

cnf(c_8614,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_8606,c_3810])).

cnf(c_4050,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1726])).

cnf(c_5601,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_4050])).

cnf(c_11933,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3810,c_5601])).

cnf(c_3070,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1729])).

cnf(c_12354,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0),X1) = iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11933,c_3070])).

cnf(c_12944,plain,
    ( v4_relat_1(k7_relat_1(sK4,k1_relat_1(sK4)),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8614,c_12354])).

cnf(c_12948,plain,
    ( v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12944,c_8606])).

cnf(c_12956,plain,
    ( v4_relat_1(sK4,X0)
    | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12948])).

cnf(c_12958,plain,
    ( v4_relat_1(sK4,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12956])).

cnf(c_2714,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_3756,plain,
    ( X0 != k2_relset_1(sK1,sK2,sK4)
    | sK3 = X0
    | sK3 != k2_relset_1(sK1,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_19457,plain,
    ( k2_relat_1(sK4) != k2_relset_1(sK1,sK2,sK4)
    | sK3 != k2_relset_1(sK1,sK2,sK4)
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3756])).

cnf(c_2166,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2374,plain,
    ( ~ r1_tarski(k1_relat_1(X0),sK1)
    | ~ r1_tarski(sK1,k1_relat_1(X0))
    | sK1 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_27408,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | sK1 = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_27409,plain,
    ( sK1 = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27408])).

cnf(c_5222,plain,
    ( X0 != X1
    | k2_relat_1(sK4) != X1
    | k2_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_11823,plain,
    ( X0 != k2_relat_1(sK4)
    | k2_relat_1(sK4) = X0
    | k2_relat_1(sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_33365,plain,
    ( k2_relat_1(sK4) != k2_relat_1(sK4)
    | k2_relat_1(sK4) = sK3
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11823])).

cnf(c_33378,plain,
    ( k2_relset_1(sK1,sK2,sK4) != k2_relat_1(sK4)
    | k2_relat_1(sK4) = k2_relset_1(sK1,sK2,sK4)
    | k2_relat_1(sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11823])).

cnf(c_33947,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relset_1(k1_relat_1(k1_relat_1(sK4)),k2_relat_1(k1_relat_1(sK4)),k1_relat_1(sK4)) = k2_relat_1(k1_relat_1(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_33922])).

cnf(c_6826,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK4),X2)
    | X2 != X1
    | k2_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_34315,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | ~ r1_tarski(sK3,X1)
    | X0 != X1
    | k2_relat_1(sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_6826])).

cnf(c_34332,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | k2_relat_1(sK4) != sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34315])).

cnf(c_34913,plain,
    ( k2_relset_1(k1_relat_1(k1_relat_1(sK4)),k2_relat_1(k1_relat_1(sK4)),k1_relat_1(sK4)) = k2_relat_1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33922,c_36,c_41,c_35,c_99,c_100,c_114,c_115,c_640,c_1982,c_1983,c_2029,c_2030,c_2076,c_2132,c_2133,c_2358,c_2423,c_2712,c_2713,c_2947,c_3698,c_3808,c_3809,c_4281,c_4282,c_4989,c_5217,c_6324,c_6342,c_8128,c_8126,c_8302,c_9486,c_9487,c_9827,c_10834,c_10835,c_12958,c_19457,c_27409,c_33365,c_33378,c_33947,c_34332])).

cnf(c_34916,plain,
    ( k2_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) = k2_relat_1(k1_relat_1(sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4440,c_34913])).

cnf(c_4924,plain,
    ( k7_relat_1(sK4,sK1) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_1730])).

cnf(c_2393,plain,
    ( ~ v4_relat_1(sK4,X0)
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0) = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4314,plain,
    ( ~ v4_relat_1(sK4,sK1)
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,sK1) = sK4 ),
    inference(instantiation,[status(thm)],[c_2393])).

cnf(c_5108,plain,
    ( k7_relat_1(sK4,sK1) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4924,c_36,c_2029,c_3809,c_4314])).

cnf(c_5111,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5108,c_3810])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1731,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5431,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5111,c_1731])).

cnf(c_5434,plain,
    ( r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5431,c_3808])).

cnf(c_5435,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5434])).

cnf(c_6341,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6339])).

cnf(c_13069,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | v4_relat_1(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12948,c_3808])).

cnf(c_13070,plain,
    ( v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13069])).

cnf(c_13071,plain,
    ( v4_relat_1(sK4,X0)
    | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13070])).

cnf(c_13073,plain,
    ( v4_relat_1(sK4,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13071])).

cnf(c_17270,plain,
    ( v1_relat_1(k1_relat_1(sK4))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17153])).

cnf(c_1737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3096,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_3070])).

cnf(c_8166,plain,
    ( v4_relat_1(X0,k1_xboole_0) != iProver_top
    | v4_relat_1(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_3096])).

cnf(c_4052,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_1736])).

cnf(c_9895,plain,
    ( v4_relat_1(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(k1_relat_1(X0)),X2) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_1735])).

cnf(c_23694,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_9895])).

cnf(c_23968,plain,
    ( v1_relat_1(k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23694,c_3808])).

cnf(c_23969,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23968])).

cnf(c_23980,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),X0) != iProver_top
    | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_23969])).

cnf(c_1740,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4961,plain,
    ( k1_relat_1(X0) = X1
    | v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1740])).

cnf(c_11601,plain,
    ( k1_relat_1(sK4) = X0
    | sK2 = k1_xboole_0
    | v4_relat_1(sK4,X0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_4961])).

cnf(c_12093,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | v4_relat_1(sK4,X0) != iProver_top
    | sK2 = k1_xboole_0
    | k1_relat_1(sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11601,c_3808])).

cnf(c_12094,plain,
    ( k1_relat_1(sK4) = X0
    | sK2 = k1_xboole_0
    | v4_relat_1(sK4,X0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12093])).

cnf(c_26910,plain,
    ( k2_zfmisc_1(X0,X1) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23980,c_12094])).

cnf(c_29251,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_26910])).

cnf(c_29258,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29251,c_5])).

cnf(c_8487,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8480,c_1720])).

cnf(c_8653,plain,
    ( v1_relat_1(k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8487,c_100,c_1983,c_2133,c_2358,c_6342])).

cnf(c_3067,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1729])).

cnf(c_7061,plain,
    ( v4_relat_1(X0,k1_xboole_0) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_3067])).

cnf(c_7250,plain,
    ( v4_relat_1(X0,k1_xboole_0) != iProver_top
    | v4_relat_1(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_7061])).

cnf(c_11067,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK1,k1_xboole_0) = iProver_top
    | v4_relat_1(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_7250])).

cnf(c_26906,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_23980])).

cnf(c_86,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_88,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_116,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_118,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_2023,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2023])).

cnf(c_2026,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_2161,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_2162,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_2164,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_1059,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_4309,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(sK4,X1)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_4310,plain,
    ( sK4 != X0
    | v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(sK4,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4309])).

cnf(c_4312,plain,
    ( sK4 != k1_xboole_0
    | v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4310])).

cnf(c_9893,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_1740])).

cnf(c_22243,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | r1_tarski(k1_relat_1(X1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_9893])).

cnf(c_22249,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22243,c_5])).

cnf(c_1738,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4855,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1740])).

cnf(c_9892,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_4052])).

cnf(c_10039,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_9892])).

cnf(c_22490,plain,
    ( r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22249,c_4855,c_10039])).

cnf(c_22491,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22490])).

cnf(c_22500,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_22491])).

cnf(c_2151,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_2152,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_2704,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2690])).

cnf(c_2232,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2773,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_2774,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2780,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2921,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2923,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK4)
    | sK4 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2921])).

cnf(c_2913,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_4636,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2913])).

cnf(c_6881,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | X0 != k2_zfmisc_1(sK1,sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4636])).

cnf(c_6883,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | r1_tarski(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_6881])).

cnf(c_1055,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_9571,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(X0,X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_9573,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9571])).

cnf(c_8108,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_22352,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | X0 = k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_8108])).

cnf(c_22354,plain,
    ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22352])).

cnf(c_22918,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22500,c_114,c_115,c_2152,c_2358,c_2704,c_2773,c_2774,c_2780,c_2923,c_3808,c_6883,c_9573,c_22354])).

cnf(c_22919,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22918])).

cnf(c_26911,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(X0,X1)) = iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23980,c_5298])).

cnf(c_27166,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_26911])).

cnf(c_27648,plain,
    ( v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26906,c_88,c_114,c_115,c_117,c_2026,c_2133,c_2163,c_2358,c_4312,c_22920])).

cnf(c_27656,plain,
    ( v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_27648])).

cnf(c_23982,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_23969])).

cnf(c_24231,plain,
    ( k2_zfmisc_1(X0,X1) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(X0,X1),sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23982,c_12094])).

cnf(c_28661,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_24231])).

cnf(c_28668,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28661,c_5])).

cnf(c_28,plain,
    ( v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_663,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK0(X0,X1) != sK4
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_196])).

cnf(c_664,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK0(sK1,sK3) != sK4 ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_2202,plain,
    ( r1_tarski(k1_xboole_0,sK0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2205,plain,
    ( r1_tarski(k1_xboole_0,sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_2207,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_22,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_529,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK1 != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_196])).

cnf(c_530,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1719,plain,
    ( sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_1898,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1719,c_4])).

cnf(c_111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_113,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_2349,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | sK4 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1898,c_113,c_118])).

cnf(c_2350,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2349])).

cnf(c_2424,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2423])).

cnf(c_32,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1723,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2598,plain,
    ( m1_subset_1(sK0(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1723])).

cnf(c_2691,plain,
    ( r1_tarski(sK0(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_1736])).

cnf(c_4859,plain,
    ( sK0(X0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK0(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2691,c_1740])).

cnf(c_4892,plain,
    ( sK0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4859])).

cnf(c_2927,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_11529,plain,
    ( sK0(X0,X1) != X2
    | sK4 != X2
    | sK4 = sK0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2927])).

cnf(c_11530,plain,
    ( sK0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK4 = sK0(k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11529])).

cnf(c_2245,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_9666,plain,
    ( sK0(sK1,sK3) != X0
    | sK0(sK1,sK3) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_18747,plain,
    ( sK0(sK1,sK3) != sK0(X0,X1)
    | sK0(sK1,sK3) = sK4
    | sK4 != sK0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_9666])).

cnf(c_18749,plain,
    ( sK0(sK1,sK3) != sK0(k1_xboole_0,k1_xboole_0)
    | sK0(sK1,sK3) = sK4
    | sK4 != sK0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18747])).

cnf(c_1064,plain,
    ( X0 != X1
    | X2 != X3
    | sK0(X0,X2) = sK0(X1,X3) ),
    theory(equality)).

cnf(c_18748,plain,
    ( sK0(sK1,sK3) = sK0(X0,X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_18750,plain,
    ( sK0(sK1,sK3) = sK0(k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18748])).

cnf(c_24232,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) = iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23982,c_5298])).

cnf(c_27068,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_24232])).

cnf(c_4988,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4960])).

cnf(c_24228,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_23982])).

cnf(c_9897,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_5309])).

cnf(c_10426,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_9897])).

cnf(c_8109,plain,
    ( k2_zfmisc_1(sK1,sK2) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8108])).

cnf(c_8275,plain,
    ( k2_zfmisc_1(sK1,sK2) != X0
    | k2_zfmisc_1(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_9570,plain,
    ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_8275])).

cnf(c_9572,plain,
    ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9570])).

cnf(c_10533,plain,
    ( v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10426,c_88,c_114,c_115,c_2026,c_2133,c_2152,c_2358,c_2704,c_2773,c_2774,c_2780,c_2923,c_4312,c_6883,c_8109,c_9572,c_9573])).

cnf(c_10541,plain,
    ( v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_10533])).

cnf(c_24841,plain,
    ( v4_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24228,c_8653,c_10541])).

cnf(c_27684,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27068,c_114,c_115,c_118,c_2164,c_2358,c_3808,c_4988,c_24841])).

cnf(c_28968,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | sK2 = k1_xboole_0
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28668,c_36,c_41,c_114,c_115,c_640,c_664,c_2029,c_2030,c_2152,c_2207,c_2350,c_2358,c_2423,c_2424,c_2704,c_2712,c_2713,c_2773,c_2774,c_2780,c_2923,c_3697,c_3698,c_3808,c_3809,c_4281,c_4282,c_4892,c_6883,c_8302,c_9486,c_9487,c_9573,c_11530,c_18749,c_18750,c_22354,c_22500,c_27409,c_27684])).

cnf(c_28969,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_28968])).

cnf(c_28975,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_28969])).

cnf(c_30441,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29258,c_3808,c_8653,c_11067,c_27656,c_28975])).

cnf(c_30448,plain,
    ( sK2 = k1_xboole_0
    | v4_relat_1(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8166,c_30441])).

cnf(c_30466,plain,
    ( ~ v4_relat_1(sK4,k1_xboole_0)
    | ~ v1_relat_1(k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_30448])).

cnf(c_35165,plain,
    ( X0 != sK3
    | k2_relat_1(sK4) = X0
    | k2_relat_1(sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_35167,plain,
    ( k2_relat_1(sK4) != sK3
    | k2_relat_1(sK4) = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_35165])).

cnf(c_35705,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34916,c_36,c_41,c_35,c_99,c_114,c_115,c_640,c_1982,c_2029,c_2030,c_2076,c_2132,c_2423,c_2712,c_2713,c_2947,c_3698,c_3808,c_3809,c_4281,c_4282,c_5217,c_5435,c_6341,c_8128,c_8126,c_8302,c_9486,c_9487,c_9827,c_10834,c_10835,c_13073,c_17270,c_19457,c_27409,c_30466,c_33365,c_33378,c_34332,c_35167])).

cnf(c_35796,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35705,c_34])).

cnf(c_35797,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_35796])).

cnf(c_1714,plain,
    ( sK0(sK1,sK3) != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_35890,plain,
    ( sK0(k1_xboole_0,sK3) != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35797,c_1714])).

cnf(c_2599,plain,
    ( m1_subset_1(sK0(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1723])).

cnf(c_2692,plain,
    ( r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_1736])).

cnf(c_5578,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2692,c_4855])).

cnf(c_35893,plain,
    ( sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35890,c_5,c_5578])).

cnf(c_22920,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22919])).

cnf(c_1057,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2087,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_2521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2087])).

cnf(c_4370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK4,k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_4371,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | sK4 != X2
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4370])).

cnf(c_4373,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4371])).

cnf(c_2163,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_1056,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1067,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_117,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35893,c_35705,c_22920,c_4373,c_2358,c_2163,c_1067,c_118,c_117,c_115,c_114,c_113])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.87/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.87/1.49  
% 7.87/1.49  ------  iProver source info
% 7.87/1.49  
% 7.87/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.87/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.87/1.49  git: non_committed_changes: false
% 7.87/1.49  git: last_make_outside_of_git: false
% 7.87/1.49  
% 7.87/1.49  ------ 
% 7.87/1.49  
% 7.87/1.49  ------ Input Options
% 7.87/1.49  
% 7.87/1.49  --out_options                           all
% 7.87/1.49  --tptp_safe_out                         true
% 7.87/1.49  --problem_path                          ""
% 7.87/1.49  --include_path                          ""
% 7.87/1.49  --clausifier                            res/vclausify_rel
% 7.87/1.49  --clausifier_options                    --mode clausify
% 7.87/1.49  --stdin                                 false
% 7.87/1.49  --stats_out                             all
% 7.87/1.49  
% 7.87/1.49  ------ General Options
% 7.87/1.49  
% 7.87/1.49  --fof                                   false
% 7.87/1.49  --time_out_real                         305.
% 7.87/1.49  --time_out_virtual                      -1.
% 7.87/1.49  --symbol_type_check                     false
% 7.87/1.49  --clausify_out                          false
% 7.87/1.49  --sig_cnt_out                           false
% 7.87/1.49  --trig_cnt_out                          false
% 7.87/1.49  --trig_cnt_out_tolerance                1.
% 7.87/1.49  --trig_cnt_out_sk_spl                   false
% 7.87/1.49  --abstr_cl_out                          false
% 7.87/1.49  
% 7.87/1.49  ------ Global Options
% 7.87/1.49  
% 7.87/1.49  --schedule                              default
% 7.87/1.49  --add_important_lit                     false
% 7.87/1.49  --prop_solver_per_cl                    1000
% 7.87/1.49  --min_unsat_core                        false
% 7.87/1.49  --soft_assumptions                      false
% 7.87/1.49  --soft_lemma_size                       3
% 7.87/1.49  --prop_impl_unit_size                   0
% 7.87/1.49  --prop_impl_unit                        []
% 7.87/1.49  --share_sel_clauses                     true
% 7.87/1.49  --reset_solvers                         false
% 7.87/1.49  --bc_imp_inh                            [conj_cone]
% 7.87/1.49  --conj_cone_tolerance                   3.
% 7.87/1.49  --extra_neg_conj                        none
% 7.87/1.49  --large_theory_mode                     true
% 7.87/1.49  --prolific_symb_bound                   200
% 7.87/1.49  --lt_threshold                          2000
% 7.87/1.49  --clause_weak_htbl                      true
% 7.87/1.49  --gc_record_bc_elim                     false
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing Options
% 7.87/1.49  
% 7.87/1.49  --preprocessing_flag                    true
% 7.87/1.49  --time_out_prep_mult                    0.1
% 7.87/1.49  --splitting_mode                        input
% 7.87/1.49  --splitting_grd                         true
% 7.87/1.49  --splitting_cvd                         false
% 7.87/1.49  --splitting_cvd_svl                     false
% 7.87/1.49  --splitting_nvd                         32
% 7.87/1.49  --sub_typing                            true
% 7.87/1.49  --prep_gs_sim                           true
% 7.87/1.49  --prep_unflatten                        true
% 7.87/1.49  --prep_res_sim                          true
% 7.87/1.49  --prep_upred                            true
% 7.87/1.49  --prep_sem_filter                       exhaustive
% 7.87/1.49  --prep_sem_filter_out                   false
% 7.87/1.49  --pred_elim                             true
% 7.87/1.49  --res_sim_input                         true
% 7.87/1.49  --eq_ax_congr_red                       true
% 7.87/1.49  --pure_diseq_elim                       true
% 7.87/1.49  --brand_transform                       false
% 7.87/1.49  --non_eq_to_eq                          false
% 7.87/1.49  --prep_def_merge                        true
% 7.87/1.49  --prep_def_merge_prop_impl              false
% 7.87/1.49  --prep_def_merge_mbd                    true
% 7.87/1.49  --prep_def_merge_tr_red                 false
% 7.87/1.49  --prep_def_merge_tr_cl                  false
% 7.87/1.49  --smt_preprocessing                     true
% 7.87/1.49  --smt_ac_axioms                         fast
% 7.87/1.49  --preprocessed_out                      false
% 7.87/1.49  --preprocessed_stats                    false
% 7.87/1.49  
% 7.87/1.49  ------ Abstraction refinement Options
% 7.87/1.49  
% 7.87/1.49  --abstr_ref                             []
% 7.87/1.49  --abstr_ref_prep                        false
% 7.87/1.49  --abstr_ref_until_sat                   false
% 7.87/1.49  --abstr_ref_sig_restrict                funpre
% 7.87/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.87/1.49  --abstr_ref_under                       []
% 7.87/1.49  
% 7.87/1.49  ------ SAT Options
% 7.87/1.49  
% 7.87/1.49  --sat_mode                              false
% 7.87/1.49  --sat_fm_restart_options                ""
% 7.87/1.49  --sat_gr_def                            false
% 7.87/1.49  --sat_epr_types                         true
% 7.87/1.49  --sat_non_cyclic_types                  false
% 7.87/1.49  --sat_finite_models                     false
% 7.87/1.49  --sat_fm_lemmas                         false
% 7.87/1.49  --sat_fm_prep                           false
% 7.87/1.49  --sat_fm_uc_incr                        true
% 7.87/1.49  --sat_out_model                         small
% 7.87/1.49  --sat_out_clauses                       false
% 7.87/1.49  
% 7.87/1.49  ------ QBF Options
% 7.87/1.49  
% 7.87/1.49  --qbf_mode                              false
% 7.87/1.49  --qbf_elim_univ                         false
% 7.87/1.49  --qbf_dom_inst                          none
% 7.87/1.49  --qbf_dom_pre_inst                      false
% 7.87/1.49  --qbf_sk_in                             false
% 7.87/1.49  --qbf_pred_elim                         true
% 7.87/1.49  --qbf_split                             512
% 7.87/1.49  
% 7.87/1.49  ------ BMC1 Options
% 7.87/1.49  
% 7.87/1.49  --bmc1_incremental                      false
% 7.87/1.49  --bmc1_axioms                           reachable_all
% 7.87/1.49  --bmc1_min_bound                        0
% 7.87/1.49  --bmc1_max_bound                        -1
% 7.87/1.49  --bmc1_max_bound_default                -1
% 7.87/1.49  --bmc1_symbol_reachability              true
% 7.87/1.49  --bmc1_property_lemmas                  false
% 7.87/1.49  --bmc1_k_induction                      false
% 7.87/1.49  --bmc1_non_equiv_states                 false
% 7.87/1.49  --bmc1_deadlock                         false
% 7.87/1.49  --bmc1_ucm                              false
% 7.87/1.49  --bmc1_add_unsat_core                   none
% 7.87/1.49  --bmc1_unsat_core_children              false
% 7.87/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.87/1.49  --bmc1_out_stat                         full
% 7.87/1.49  --bmc1_ground_init                      false
% 7.87/1.49  --bmc1_pre_inst_next_state              false
% 7.87/1.49  --bmc1_pre_inst_state                   false
% 7.87/1.49  --bmc1_pre_inst_reach_state             false
% 7.87/1.49  --bmc1_out_unsat_core                   false
% 7.87/1.49  --bmc1_aig_witness_out                  false
% 7.87/1.49  --bmc1_verbose                          false
% 7.87/1.49  --bmc1_dump_clauses_tptp                false
% 7.87/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.87/1.49  --bmc1_dump_file                        -
% 7.87/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.87/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.87/1.49  --bmc1_ucm_extend_mode                  1
% 7.87/1.49  --bmc1_ucm_init_mode                    2
% 7.87/1.49  --bmc1_ucm_cone_mode                    none
% 7.87/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.87/1.49  --bmc1_ucm_relax_model                  4
% 7.87/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.87/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.87/1.49  --bmc1_ucm_layered_model                none
% 7.87/1.49  --bmc1_ucm_max_lemma_size               10
% 7.87/1.49  
% 7.87/1.49  ------ AIG Options
% 7.87/1.49  
% 7.87/1.49  --aig_mode                              false
% 7.87/1.49  
% 7.87/1.49  ------ Instantiation Options
% 7.87/1.49  
% 7.87/1.49  --instantiation_flag                    true
% 7.87/1.49  --inst_sos_flag                         false
% 7.87/1.49  --inst_sos_phase                        true
% 7.87/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.87/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.87/1.49  --inst_lit_sel_side                     num_symb
% 7.87/1.49  --inst_solver_per_active                1400
% 7.87/1.49  --inst_solver_calls_frac                1.
% 7.87/1.49  --inst_passive_queue_type               priority_queues
% 7.87/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.87/1.49  --inst_passive_queues_freq              [25;2]
% 7.87/1.49  --inst_dismatching                      true
% 7.87/1.49  --inst_eager_unprocessed_to_passive     true
% 7.87/1.49  --inst_prop_sim_given                   true
% 7.87/1.49  --inst_prop_sim_new                     false
% 7.87/1.49  --inst_subs_new                         false
% 7.87/1.49  --inst_eq_res_simp                      false
% 7.87/1.49  --inst_subs_given                       false
% 7.87/1.49  --inst_orphan_elimination               true
% 7.87/1.49  --inst_learning_loop_flag               true
% 7.87/1.49  --inst_learning_start                   3000
% 7.87/1.49  --inst_learning_factor                  2
% 7.87/1.49  --inst_start_prop_sim_after_learn       3
% 7.87/1.49  --inst_sel_renew                        solver
% 7.87/1.49  --inst_lit_activity_flag                true
% 7.87/1.49  --inst_restr_to_given                   false
% 7.87/1.49  --inst_activity_threshold               500
% 7.87/1.49  --inst_out_proof                        true
% 7.87/1.49  
% 7.87/1.49  ------ Resolution Options
% 7.87/1.49  
% 7.87/1.49  --resolution_flag                       true
% 7.87/1.49  --res_lit_sel                           adaptive
% 7.87/1.49  --res_lit_sel_side                      none
% 7.87/1.49  --res_ordering                          kbo
% 7.87/1.49  --res_to_prop_solver                    active
% 7.87/1.49  --res_prop_simpl_new                    false
% 7.87/1.49  --res_prop_simpl_given                  true
% 7.87/1.49  --res_passive_queue_type                priority_queues
% 7.87/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.49  --res_passive_queues_freq               [15;5]
% 7.87/1.49  --res_forward_subs                      full
% 7.87/1.49  --res_backward_subs                     full
% 7.87/1.49  --res_forward_subs_resolution           true
% 7.87/1.49  --res_backward_subs_resolution          true
% 7.87/1.49  --res_orphan_elimination                true
% 7.87/1.49  --res_time_limit                        2.
% 7.87/1.49  --res_out_proof                         true
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Options
% 7.87/1.49  
% 7.87/1.49  --superposition_flag                    true
% 7.87/1.49  --sup_passive_queue_type                priority_queues
% 7.87/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.49  --demod_completeness_check              fast
% 7.87/1.49  --demod_use_ground                      true
% 7.87/1.49  --sup_to_prop_solver                    passive
% 7.87/1.49  --sup_prop_simpl_new                    true
% 7.87/1.49  --sup_prop_simpl_given                  true
% 7.87/1.49  --sup_fun_splitting                     false
% 7.87/1.49  --sup_smt_interval                      50000
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Simplification Setup
% 7.87/1.49  
% 7.87/1.49  --sup_indices_passive                   []
% 7.87/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.87/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.49  --sup_full_bw                           [BwDemod]
% 7.87/1.49  --sup_immed_triv                        [TrivRules]
% 7.87/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.49  --sup_immed_bw_main                     []
% 7.87/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.87/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.87/1.49  
% 7.87/1.49  ------ Combination Options
% 7.87/1.49  
% 7.87/1.49  --comb_res_mult                         3
% 7.87/1.49  --comb_sup_mult                         2
% 7.87/1.49  --comb_inst_mult                        10
% 7.87/1.49  
% 7.87/1.49  ------ Debug Options
% 7.87/1.49  
% 7.87/1.49  --dbg_backtrace                         false
% 7.87/1.49  --dbg_dump_prop_clauses                 false
% 7.87/1.49  --dbg_dump_prop_clauses_file            -
% 7.87/1.49  --dbg_out_stat                          false
% 7.87/1.49  ------ Parsing...
% 7.87/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.87/1.49  ------ Proving...
% 7.87/1.49  ------ Problem Properties 
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  clauses                                 38
% 7.87/1.49  conjectures                             3
% 7.87/1.49  EPR                                     5
% 7.87/1.49  Horn                                    33
% 7.87/1.49  unary                                   13
% 7.87/1.49  binary                                  12
% 7.87/1.49  lits                                    82
% 7.87/1.49  lits eq                                 37
% 7.87/1.49  fd_pure                                 0
% 7.87/1.49  fd_pseudo                               0
% 7.87/1.49  fd_cond                                 3
% 7.87/1.49  fd_pseudo_cond                          1
% 7.87/1.49  AC symbols                              0
% 7.87/1.49  
% 7.87/1.49  ------ Schedule dynamic 5 is on 
% 7.87/1.49  
% 7.87/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  ------ 
% 7.87/1.49  Current options:
% 7.87/1.49  ------ 
% 7.87/1.49  
% 7.87/1.49  ------ Input Options
% 7.87/1.49  
% 7.87/1.49  --out_options                           all
% 7.87/1.49  --tptp_safe_out                         true
% 7.87/1.49  --problem_path                          ""
% 7.87/1.49  --include_path                          ""
% 7.87/1.49  --clausifier                            res/vclausify_rel
% 7.87/1.49  --clausifier_options                    --mode clausify
% 7.87/1.49  --stdin                                 false
% 7.87/1.49  --stats_out                             all
% 7.87/1.49  
% 7.87/1.49  ------ General Options
% 7.87/1.49  
% 7.87/1.49  --fof                                   false
% 7.87/1.49  --time_out_real                         305.
% 7.87/1.49  --time_out_virtual                      -1.
% 7.87/1.49  --symbol_type_check                     false
% 7.87/1.49  --clausify_out                          false
% 7.87/1.49  --sig_cnt_out                           false
% 7.87/1.49  --trig_cnt_out                          false
% 7.87/1.49  --trig_cnt_out_tolerance                1.
% 7.87/1.49  --trig_cnt_out_sk_spl                   false
% 7.87/1.49  --abstr_cl_out                          false
% 7.87/1.49  
% 7.87/1.49  ------ Global Options
% 7.87/1.49  
% 7.87/1.49  --schedule                              default
% 7.87/1.49  --add_important_lit                     false
% 7.87/1.49  --prop_solver_per_cl                    1000
% 7.87/1.49  --min_unsat_core                        false
% 7.87/1.49  --soft_assumptions                      false
% 7.87/1.49  --soft_lemma_size                       3
% 7.87/1.49  --prop_impl_unit_size                   0
% 7.87/1.49  --prop_impl_unit                        []
% 7.87/1.49  --share_sel_clauses                     true
% 7.87/1.49  --reset_solvers                         false
% 7.87/1.49  --bc_imp_inh                            [conj_cone]
% 7.87/1.49  --conj_cone_tolerance                   3.
% 7.87/1.49  --extra_neg_conj                        none
% 7.87/1.49  --large_theory_mode                     true
% 7.87/1.49  --prolific_symb_bound                   200
% 7.87/1.49  --lt_threshold                          2000
% 7.87/1.49  --clause_weak_htbl                      true
% 7.87/1.49  --gc_record_bc_elim                     false
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing Options
% 7.87/1.49  
% 7.87/1.49  --preprocessing_flag                    true
% 7.87/1.49  --time_out_prep_mult                    0.1
% 7.87/1.49  --splitting_mode                        input
% 7.87/1.49  --splitting_grd                         true
% 7.87/1.49  --splitting_cvd                         false
% 7.87/1.49  --splitting_cvd_svl                     false
% 7.87/1.49  --splitting_nvd                         32
% 7.87/1.49  --sub_typing                            true
% 7.87/1.49  --prep_gs_sim                           true
% 7.87/1.49  --prep_unflatten                        true
% 7.87/1.49  --prep_res_sim                          true
% 7.87/1.49  --prep_upred                            true
% 7.87/1.49  --prep_sem_filter                       exhaustive
% 7.87/1.49  --prep_sem_filter_out                   false
% 7.87/1.49  --pred_elim                             true
% 7.87/1.49  --res_sim_input                         true
% 7.87/1.49  --eq_ax_congr_red                       true
% 7.87/1.49  --pure_diseq_elim                       true
% 7.87/1.49  --brand_transform                       false
% 7.87/1.49  --non_eq_to_eq                          false
% 7.87/1.49  --prep_def_merge                        true
% 7.87/1.49  --prep_def_merge_prop_impl              false
% 7.87/1.49  --prep_def_merge_mbd                    true
% 7.87/1.49  --prep_def_merge_tr_red                 false
% 7.87/1.49  --prep_def_merge_tr_cl                  false
% 7.87/1.49  --smt_preprocessing                     true
% 7.87/1.49  --smt_ac_axioms                         fast
% 7.87/1.49  --preprocessed_out                      false
% 7.87/1.49  --preprocessed_stats                    false
% 7.87/1.49  
% 7.87/1.49  ------ Abstraction refinement Options
% 7.87/1.49  
% 7.87/1.49  --abstr_ref                             []
% 7.87/1.49  --abstr_ref_prep                        false
% 7.87/1.49  --abstr_ref_until_sat                   false
% 7.87/1.49  --abstr_ref_sig_restrict                funpre
% 7.87/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.87/1.49  --abstr_ref_under                       []
% 7.87/1.49  
% 7.87/1.49  ------ SAT Options
% 7.87/1.49  
% 7.87/1.49  --sat_mode                              false
% 7.87/1.49  --sat_fm_restart_options                ""
% 7.87/1.49  --sat_gr_def                            false
% 7.87/1.49  --sat_epr_types                         true
% 7.87/1.49  --sat_non_cyclic_types                  false
% 7.87/1.49  --sat_finite_models                     false
% 7.87/1.49  --sat_fm_lemmas                         false
% 7.87/1.49  --sat_fm_prep                           false
% 7.87/1.49  --sat_fm_uc_incr                        true
% 7.87/1.49  --sat_out_model                         small
% 7.87/1.49  --sat_out_clauses                       false
% 7.87/1.49  
% 7.87/1.49  ------ QBF Options
% 7.87/1.49  
% 7.87/1.49  --qbf_mode                              false
% 7.87/1.49  --qbf_elim_univ                         false
% 7.87/1.49  --qbf_dom_inst                          none
% 7.87/1.49  --qbf_dom_pre_inst                      false
% 7.87/1.49  --qbf_sk_in                             false
% 7.87/1.49  --qbf_pred_elim                         true
% 7.87/1.49  --qbf_split                             512
% 7.87/1.49  
% 7.87/1.49  ------ BMC1 Options
% 7.87/1.49  
% 7.87/1.49  --bmc1_incremental                      false
% 7.87/1.49  --bmc1_axioms                           reachable_all
% 7.87/1.49  --bmc1_min_bound                        0
% 7.87/1.49  --bmc1_max_bound                        -1
% 7.87/1.49  --bmc1_max_bound_default                -1
% 7.87/1.49  --bmc1_symbol_reachability              true
% 7.87/1.49  --bmc1_property_lemmas                  false
% 7.87/1.49  --bmc1_k_induction                      false
% 7.87/1.49  --bmc1_non_equiv_states                 false
% 7.87/1.49  --bmc1_deadlock                         false
% 7.87/1.49  --bmc1_ucm                              false
% 7.87/1.49  --bmc1_add_unsat_core                   none
% 7.87/1.49  --bmc1_unsat_core_children              false
% 7.87/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.87/1.49  --bmc1_out_stat                         full
% 7.87/1.49  --bmc1_ground_init                      false
% 7.87/1.49  --bmc1_pre_inst_next_state              false
% 7.87/1.49  --bmc1_pre_inst_state                   false
% 7.87/1.49  --bmc1_pre_inst_reach_state             false
% 7.87/1.49  --bmc1_out_unsat_core                   false
% 7.87/1.49  --bmc1_aig_witness_out                  false
% 7.87/1.49  --bmc1_verbose                          false
% 7.87/1.49  --bmc1_dump_clauses_tptp                false
% 7.87/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.87/1.49  --bmc1_dump_file                        -
% 7.87/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.87/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.87/1.49  --bmc1_ucm_extend_mode                  1
% 7.87/1.49  --bmc1_ucm_init_mode                    2
% 7.87/1.49  --bmc1_ucm_cone_mode                    none
% 7.87/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.87/1.49  --bmc1_ucm_relax_model                  4
% 7.87/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.87/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.87/1.49  --bmc1_ucm_layered_model                none
% 7.87/1.49  --bmc1_ucm_max_lemma_size               10
% 7.87/1.49  
% 7.87/1.49  ------ AIG Options
% 7.87/1.49  
% 7.87/1.49  --aig_mode                              false
% 7.87/1.49  
% 7.87/1.49  ------ Instantiation Options
% 7.87/1.49  
% 7.87/1.49  --instantiation_flag                    true
% 7.87/1.49  --inst_sos_flag                         false
% 7.87/1.49  --inst_sos_phase                        true
% 7.87/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.87/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.87/1.49  --inst_lit_sel_side                     none
% 7.87/1.49  --inst_solver_per_active                1400
% 7.87/1.49  --inst_solver_calls_frac                1.
% 7.87/1.49  --inst_passive_queue_type               priority_queues
% 7.87/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.87/1.49  --inst_passive_queues_freq              [25;2]
% 7.87/1.49  --inst_dismatching                      true
% 7.87/1.49  --inst_eager_unprocessed_to_passive     true
% 7.87/1.49  --inst_prop_sim_given                   true
% 7.87/1.49  --inst_prop_sim_new                     false
% 7.87/1.49  --inst_subs_new                         false
% 7.87/1.49  --inst_eq_res_simp                      false
% 7.87/1.49  --inst_subs_given                       false
% 7.87/1.49  --inst_orphan_elimination               true
% 7.87/1.49  --inst_learning_loop_flag               true
% 7.87/1.49  --inst_learning_start                   3000
% 7.87/1.49  --inst_learning_factor                  2
% 7.87/1.49  --inst_start_prop_sim_after_learn       3
% 7.87/1.49  --inst_sel_renew                        solver
% 7.87/1.49  --inst_lit_activity_flag                true
% 7.87/1.49  --inst_restr_to_given                   false
% 7.87/1.49  --inst_activity_threshold               500
% 7.87/1.49  --inst_out_proof                        true
% 7.87/1.49  
% 7.87/1.49  ------ Resolution Options
% 7.87/1.49  
% 7.87/1.49  --resolution_flag                       false
% 7.87/1.49  --res_lit_sel                           adaptive
% 7.87/1.49  --res_lit_sel_side                      none
% 7.87/1.49  --res_ordering                          kbo
% 7.87/1.49  --res_to_prop_solver                    active
% 7.87/1.49  --res_prop_simpl_new                    false
% 7.87/1.49  --res_prop_simpl_given                  true
% 7.87/1.49  --res_passive_queue_type                priority_queues
% 7.87/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.49  --res_passive_queues_freq               [15;5]
% 7.87/1.49  --res_forward_subs                      full
% 7.87/1.49  --res_backward_subs                     full
% 7.87/1.49  --res_forward_subs_resolution           true
% 7.87/1.49  --res_backward_subs_resolution          true
% 7.87/1.49  --res_orphan_elimination                true
% 7.87/1.49  --res_time_limit                        2.
% 7.87/1.49  --res_out_proof                         true
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Options
% 7.87/1.49  
% 7.87/1.49  --superposition_flag                    true
% 7.87/1.49  --sup_passive_queue_type                priority_queues
% 7.87/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.49  --demod_completeness_check              fast
% 7.87/1.49  --demod_use_ground                      true
% 7.87/1.49  --sup_to_prop_solver                    passive
% 7.87/1.49  --sup_prop_simpl_new                    true
% 7.87/1.49  --sup_prop_simpl_given                  true
% 7.87/1.49  --sup_fun_splitting                     false
% 7.87/1.49  --sup_smt_interval                      50000
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Simplification Setup
% 7.87/1.49  
% 7.87/1.49  --sup_indices_passive                   []
% 7.87/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.87/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.49  --sup_full_bw                           [BwDemod]
% 7.87/1.49  --sup_immed_triv                        [TrivRules]
% 7.87/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.49  --sup_immed_bw_main                     []
% 7.87/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.87/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.87/1.49  
% 7.87/1.49  ------ Combination Options
% 7.87/1.49  
% 7.87/1.49  --comb_res_mult                         3
% 7.87/1.49  --comb_sup_mult                         2
% 7.87/1.49  --comb_inst_mult                        10
% 7.87/1.49  
% 7.87/1.49  ------ Debug Options
% 7.87/1.49  
% 7.87/1.49  --dbg_backtrace                         false
% 7.87/1.49  --dbg_dump_prop_clauses                 false
% 7.87/1.49  --dbg_dump_prop_clauses_file            -
% 7.87/1.49  --dbg_out_stat                          false
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  ------ Proving...
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  % SZS status Theorem for theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  fof(f16,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f34,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(ennf_transformation,[],[f16])).
% 7.87/1.49  
% 7.87/1.49  fof(f35,plain,(
% 7.87/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(flattening,[],[f34])).
% 7.87/1.49  
% 7.87/1.49  fof(f44,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(nnf_transformation,[],[f35])).
% 7.87/1.49  
% 7.87/1.49  fof(f71,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f44])).
% 7.87/1.49  
% 7.87/1.49  fof(f18,conjecture,(
% 7.87/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f19,negated_conjecture,(
% 7.87/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.87/1.49    inference(negated_conjecture,[],[f18])).
% 7.87/1.49  
% 7.87/1.49  fof(f36,plain,(
% 7.87/1.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.87/1.49    inference(ennf_transformation,[],[f19])).
% 7.87/1.49  
% 7.87/1.49  fof(f37,plain,(
% 7.87/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.87/1.49    inference(flattening,[],[f36])).
% 7.87/1.49  
% 7.87/1.49  fof(f47,plain,(
% 7.87/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f48,plain,(
% 7.87/1.49    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 7.87/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f47])).
% 7.87/1.49  
% 7.87/1.49  fof(f83,plain,(
% 7.87/1.49    v1_funct_2(sK4,sK1,sK2)),
% 7.87/1.49    inference(cnf_transformation,[],[f48])).
% 7.87/1.49  
% 7.87/1.49  fof(f84,plain,(
% 7.87/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.87/1.49    inference(cnf_transformation,[],[f48])).
% 7.87/1.49  
% 7.87/1.49  fof(f13,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f30,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(ennf_transformation,[],[f13])).
% 7.87/1.49  
% 7.87/1.49  fof(f68,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f30])).
% 7.87/1.49  
% 7.87/1.49  fof(f12,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f20,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.87/1.49    inference(pure_predicate_removal,[],[f12])).
% 7.87/1.49  
% 7.87/1.49  fof(f29,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(ennf_transformation,[],[f20])).
% 7.87/1.49  
% 7.87/1.49  fof(f67,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f29])).
% 7.87/1.49  
% 7.87/1.49  fof(f6,axiom,(
% 7.87/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f23,plain,(
% 7.87/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(ennf_transformation,[],[f6])).
% 7.87/1.49  
% 7.87/1.49  fof(f43,plain,(
% 7.87/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(nnf_transformation,[],[f23])).
% 7.87/1.49  
% 7.87/1.49  fof(f59,plain,(
% 7.87/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f43])).
% 7.87/1.49  
% 7.87/1.49  fof(f5,axiom,(
% 7.87/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f22,plain,(
% 7.87/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.87/1.49    inference(ennf_transformation,[],[f5])).
% 7.87/1.49  
% 7.87/1.49  fof(f58,plain,(
% 7.87/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f22])).
% 7.87/1.49  
% 7.87/1.49  fof(f4,axiom,(
% 7.87/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f42,plain,(
% 7.87/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.87/1.49    inference(nnf_transformation,[],[f4])).
% 7.87/1.49  
% 7.87/1.49  fof(f57,plain,(
% 7.87/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f42])).
% 7.87/1.49  
% 7.87/1.49  fof(f56,plain,(
% 7.87/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f42])).
% 7.87/1.49  
% 7.87/1.49  fof(f7,axiom,(
% 7.87/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f61,plain,(
% 7.87/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f7])).
% 7.87/1.49  
% 7.87/1.49  fof(f1,axiom,(
% 7.87/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f38,plain,(
% 7.87/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.87/1.49    inference(nnf_transformation,[],[f1])).
% 7.87/1.49  
% 7.87/1.49  fof(f39,plain,(
% 7.87/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.87/1.49    inference(flattening,[],[f38])).
% 7.87/1.49  
% 7.87/1.49  fof(f50,plain,(
% 7.87/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.87/1.49    inference(cnf_transformation,[],[f39])).
% 7.87/1.49  
% 7.87/1.49  fof(f88,plain,(
% 7.87/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.87/1.49    inference(equality_resolution,[],[f50])).
% 7.87/1.49  
% 7.87/1.49  fof(f15,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f32,plain,(
% 7.87/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.87/1.49    inference(ennf_transformation,[],[f15])).
% 7.87/1.49  
% 7.87/1.49  fof(f33,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.87/1.49    inference(flattening,[],[f32])).
% 7.87/1.49  
% 7.87/1.49  fof(f70,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f33])).
% 7.87/1.49  
% 7.87/1.49  fof(f14,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f31,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(ennf_transformation,[],[f14])).
% 7.87/1.49  
% 7.87/1.49  fof(f69,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f31])).
% 7.87/1.49  
% 7.87/1.49  fof(f85,plain,(
% 7.87/1.49    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 7.87/1.49    inference(cnf_transformation,[],[f48])).
% 7.87/1.49  
% 7.87/1.49  fof(f3,axiom,(
% 7.87/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f40,plain,(
% 7.87/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.87/1.49    inference(nnf_transformation,[],[f3])).
% 7.87/1.49  
% 7.87/1.49  fof(f41,plain,(
% 7.87/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.87/1.49    inference(flattening,[],[f40])).
% 7.87/1.49  
% 7.87/1.49  fof(f53,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f41])).
% 7.87/1.49  
% 7.87/1.49  fof(f54,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.87/1.49    inference(cnf_transformation,[],[f41])).
% 7.87/1.49  
% 7.87/1.49  fof(f91,plain,(
% 7.87/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.87/1.49    inference(equality_resolution,[],[f54])).
% 7.87/1.49  
% 7.87/1.49  fof(f73,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f44])).
% 7.87/1.49  
% 7.87/1.49  fof(f87,plain,(
% 7.87/1.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 7.87/1.49    inference(cnf_transformation,[],[f48])).
% 7.87/1.49  
% 7.87/1.49  fof(f82,plain,(
% 7.87/1.49    v1_funct_1(sK4)),
% 7.87/1.49    inference(cnf_transformation,[],[f48])).
% 7.87/1.49  
% 7.87/1.49  fof(f2,axiom,(
% 7.87/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f52,plain,(
% 7.87/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f2])).
% 7.87/1.49  
% 7.87/1.49  fof(f75,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f44])).
% 7.87/1.49  
% 7.87/1.49  fof(f94,plain,(
% 7.87/1.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.87/1.49    inference(equality_resolution,[],[f75])).
% 7.87/1.49  
% 7.87/1.49  fof(f55,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.87/1.49    inference(cnf_transformation,[],[f41])).
% 7.87/1.49  
% 7.87/1.49  fof(f90,plain,(
% 7.87/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.87/1.49    inference(equality_resolution,[],[f55])).
% 7.87/1.49  
% 7.87/1.49  fof(f86,plain,(
% 7.87/1.49    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 7.87/1.49    inference(cnf_transformation,[],[f48])).
% 7.87/1.49  
% 7.87/1.49  fof(f51,plain,(
% 7.87/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f39])).
% 7.87/1.49  
% 7.87/1.49  fof(f60,plain,(
% 7.87/1.49    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f43])).
% 7.87/1.49  
% 7.87/1.49  fof(f10,axiom,(
% 7.87/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f27,plain,(
% 7.87/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.87/1.49    inference(ennf_transformation,[],[f10])).
% 7.87/1.49  
% 7.87/1.49  fof(f28,plain,(
% 7.87/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(flattening,[],[f27])).
% 7.87/1.49  
% 7.87/1.49  fof(f64,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f28])).
% 7.87/1.49  
% 7.87/1.49  fof(f8,axiom,(
% 7.87/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f24,plain,(
% 7.87/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(ennf_transformation,[],[f8])).
% 7.87/1.49  
% 7.87/1.49  fof(f62,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f24])).
% 7.87/1.49  
% 7.87/1.49  fof(f9,axiom,(
% 7.87/1.49    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f25,plain,(
% 7.87/1.49    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(ennf_transformation,[],[f9])).
% 7.87/1.49  
% 7.87/1.49  fof(f26,plain,(
% 7.87/1.49    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 7.87/1.49    inference(flattening,[],[f25])).
% 7.87/1.49  
% 7.87/1.49  fof(f63,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f26])).
% 7.87/1.49  
% 7.87/1.49  fof(f17,axiom,(
% 7.87/1.49    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f21,plain,(
% 7.87/1.49    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(pure_predicate_removal,[],[f17])).
% 7.87/1.49  
% 7.87/1.49  fof(f45,plain,(
% 7.87/1.49    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f46,plain,(
% 7.87/1.49    ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f45])).
% 7.87/1.49  
% 7.87/1.49  fof(f81,plain,(
% 7.87/1.49    ( ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f46])).
% 7.87/1.49  
% 7.87/1.49  fof(f76,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f44])).
% 7.87/1.49  
% 7.87/1.49  fof(f92,plain,(
% 7.87/1.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(equality_resolution,[],[f76])).
% 7.87/1.49  
% 7.87/1.49  fof(f93,plain,(
% 7.87/1.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.87/1.49    inference(equality_resolution,[],[f92])).
% 7.87/1.49  
% 7.87/1.49  fof(f77,plain,(
% 7.87/1.49    ( ! [X0,X1] : (m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f46])).
% 7.87/1.49  
% 7.87/1.49  cnf(c_27,plain,
% 7.87/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.87/1.49      | k1_xboole_0 = X2 ),
% 7.87/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_37,negated_conjecture,
% 7.87/1.49      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.87/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_652,plain,
% 7.87/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.87/1.49      | sK2 != X2
% 7.87/1.49      | sK1 != X1
% 7.87/1.49      | sK4 != X0
% 7.87/1.49      | k1_xboole_0 = X2 ),
% 7.87/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_653,plain,
% 7.87/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.87/1.49      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.87/1.49      | k1_xboole_0 = sK2 ),
% 7.87/1.49      inference(unflattening,[status(thm)],[c_652]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_36,negated_conjecture,
% 7.87/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.87/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_655,plain,
% 7.87/1.49      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_653,c_36]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1721,plain,
% 7.87/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_19,plain,
% 7.87/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1728,plain,
% 7.87/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.87/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4180,plain,
% 7.87/1.49      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1721,c_1728]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4440,plain,
% 7.87/1.49      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_655,c_4180]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_18,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1)
% 7.87/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.87/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1729,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.87/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3069,plain,
% 7.87/1.49      ( v4_relat_1(sK4,sK1) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1721,c_1729]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_11,plain,
% 7.87/1.49      ( ~ v4_relat_1(X0,X1)
% 7.87/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.87/1.49      | ~ v1_relat_1(X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1734,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_9,plain,
% 7.87/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.87/1.49      | ~ v1_relat_1(X1)
% 7.87/1.49      | v1_relat_1(X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_7,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.87/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_268,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.87/1.49      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_269,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_268]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_331,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.87/1.49      inference(bin_hyper_res,[status(thm)],[c_9,c_269]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1720,plain,
% 7.87/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4962,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top
% 7.87/1.49      | v1_relat_1(X1) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1734,c_1720]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_17153,plain,
% 7.87/1.49      ( v1_relat_1(k1_relat_1(sK4)) = iProver_top
% 7.87/1.49      | v1_relat_1(sK1) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3069,c_4962]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8,plain,
% 7.87/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.87/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1736,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.87/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2690,plain,
% 7.87/1.49      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1721,c_1736]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3295,plain,
% 7.87/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_2690,c_1720]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12,plain,
% 7.87/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.87/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1733,plain,
% 7.87/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3808,plain,
% 7.87/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.87/1.49      inference(forward_subsumption_resolution,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_3295,c_1733]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_17497,plain,
% 7.87/1.49      ( v1_relat_1(sK1) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) = iProver_top ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_17153,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_17498,plain,
% 7.87/1.49      ( v1_relat_1(k1_relat_1(sK4)) = iProver_top
% 7.87/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_17497]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1,plain,
% 7.87/1.49      ( r1_tarski(X0,X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1739,plain,
% 7.87/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_21,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.87/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.87/1.49      | ~ v1_relat_1(X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1726,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_20,plain,
% 7.87/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1727,plain,
% 7.87/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.87/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4053,plain,
% 7.87/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.87/1.49      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 7.87/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1726,c_1727]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_33697,plain,
% 7.87/1.49      ( k2_relset_1(X0,k2_relat_1(X1),X1) = k2_relat_1(X1)
% 7.87/1.49      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.87/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1739,c_4053]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_33833,plain,
% 7.87/1.49      ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1739,c_33697]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_33922,plain,
% 7.87/1.49      ( k2_relset_1(k1_relat_1(k1_relat_1(sK4)),k2_relat_1(k1_relat_1(sK4)),k1_relat_1(sK4)) = k2_relat_1(k1_relat_1(sK4))
% 7.87/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_17498,c_33833]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_41,plain,
% 7.87/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_35,negated_conjecture,
% 7.87/1.49      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 7.87/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_99,plain,
% 7.87/1.49      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_98,plain,
% 7.87/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_100,plain,
% 7.87/1.49      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_98]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6,plain,
% 7.87/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.87/1.49      | k1_xboole_0 = X1
% 7.87/1.49      | k1_xboole_0 = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_114,plain,
% 7.87/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.87/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5,plain,
% 7.87/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_115,plain,
% 7.87/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_25,plain,
% 7.87/1.49      ( v1_funct_2(X0,X1,X2)
% 7.87/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.87/1.49      | k1_xboole_0 = X2 ),
% 7.87/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_33,negated_conjecture,
% 7.87/1.49      ( ~ v1_funct_2(sK4,sK1,sK3)
% 7.87/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.49      | ~ v1_funct_1(sK4) ),
% 7.87/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_38,negated_conjecture,
% 7.87/1.49      ( v1_funct_1(sK4) ),
% 7.87/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_195,plain,
% 7.87/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.49      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_33,c_38]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_196,negated_conjecture,
% 7.87/1.49      ( ~ v1_funct_2(sK4,sK1,sK3)
% 7.87/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_195]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_639,plain,
% 7.87/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.87/1.49      | sK3 != X2
% 7.87/1.49      | sK1 != X1
% 7.87/1.49      | sK4 != X0
% 7.87/1.49      | k1_xboole_0 = X2 ),
% 7.87/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_196]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_640,plain,
% 7.87/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.49      | k1_relset_1(sK1,sK3,sK4) != sK1
% 7.87/1.49      | k1_xboole_0 = sK3 ),
% 7.87/1.49      inference(unflattening,[status(thm)],[c_639]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1980,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.87/1.49      | v1_relat_1(X0)
% 7.87/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_331]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1982,plain,
% 7.87/1.49      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.87/1.49      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.87/1.49      | v1_relat_1(k1_xboole_0) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1980]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1981,plain,
% 7.87/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) = iProver_top
% 7.87/1.49      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1983,plain,
% 7.87/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.87/1.49      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1981]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2029,plain,
% 7.87/1.49      ( v4_relat_1(sK4,sK1)
% 7.87/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2030,plain,
% 7.87/1.49      ( v4_relat_1(sK4,sK1) = iProver_top
% 7.87/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_2029]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2076,plain,
% 7.87/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.87/1.49      | k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3,plain,
% 7.87/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2128,plain,
% 7.87/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2132,plain,
% 7.87/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2128]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2131,plain,
% 7.87/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2133,plain,
% 7.87/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2131]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_23,plain,
% 7.87/1.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.87/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.87/1.49      | k1_xboole_0 = X1
% 7.87/1.49      | k1_xboole_0 = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_567,plain,
% 7.87/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.87/1.49      | sK2 != k1_xboole_0
% 7.87/1.49      | sK1 != X1
% 7.87/1.49      | sK4 != X0
% 7.87/1.49      | k1_xboole_0 = X1
% 7.87/1.49      | k1_xboole_0 = X0 ),
% 7.87/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_37]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_568,plain,
% 7.87/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 7.87/1.49      | sK2 != k1_xboole_0
% 7.87/1.49      | k1_xboole_0 = sK1
% 7.87/1.49      | k1_xboole_0 = sK4 ),
% 7.87/1.49      inference(unflattening,[status(thm)],[c_567]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1718,plain,
% 7.87/1.49      ( sK2 != k1_xboole_0
% 7.87/1.49      | k1_xboole_0 = sK1
% 7.87/1.49      | k1_xboole_0 = sK4
% 7.87/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4,plain,
% 7.87/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1864,plain,
% 7.87/1.49      ( sK2 != k1_xboole_0
% 7.87/1.49      | sK1 = k1_xboole_0
% 7.87/1.49      | sK4 = k1_xboole_0
% 7.87/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_1718,c_4]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_34,negated_conjecture,
% 7.87/1.49      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 7.87/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1053,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2046,plain,
% 7.87/1.49      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2169,plain,
% 7.87/1.49      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2046]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1052,plain,( X0 = X0 ),theory(equality) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2170,plain,
% 7.87/1.49      ( sK1 = sK1 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1052]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2276,plain,
% 7.87/1.49      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2277,plain,
% 7.87/1.49      ( sK2 != k1_xboole_0
% 7.87/1.49      | k1_xboole_0 = sK2
% 7.87/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2276]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2358,plain,
% 7.87/1.49      ( sK2 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_1864,c_34,c_114,c_115,c_2169,c_2170,c_2277]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2423,plain,
% 7.87/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.49      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 7.87/1.49      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 7.87/1.49      | ~ v1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2281,plain,
% 7.87/1.49      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2712,plain,
% 7.87/1.49      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2281]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2713,plain,
% 7.87/1.49      ( sK3 = sK3 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1052]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_0,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.87/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2709,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2947,plain,
% 7.87/1.49      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
% 7.87/1.49      | ~ r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
% 7.87/1.49      | sK3 = k2_relset_1(sK1,sK2,sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2709]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3345,plain,
% 7.87/1.49      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1721,c_1727]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1722,plain,
% 7.87/1.49      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3697,plain,
% 7.87/1.49      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_3345,c_1722]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3698,plain,
% 7.87/1.49      ( r1_tarski(k2_relat_1(sK4),sK3) ),
% 7.87/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3697]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3809,plain,
% 7.87/1.49      ( v1_relat_1(sK4) ),
% 7.87/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2373,plain,
% 7.87/1.49      ( ~ v4_relat_1(X0,sK1)
% 7.87/1.49      | r1_tarski(k1_relat_1(X0),sK1)
% 7.87/1.49      | ~ v1_relat_1(X0) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4281,plain,
% 7.87/1.49      ( ~ v4_relat_1(sK4,sK1)
% 7.87/1.49      | r1_tarski(k1_relat_1(sK4),sK1)
% 7.87/1.49      | ~ v1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2373]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4282,plain,
% 7.87/1.49      ( v4_relat_1(sK4,sK1) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_4281]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4960,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,X0) != iProver_top
% 7.87/1.49      | r1_tarski(sK1,X0) = iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4440,c_1734]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4987,plain,
% 7.87/1.49      ( ~ v4_relat_1(sK4,X0)
% 7.87/1.49      | r1_tarski(sK1,X0)
% 7.87/1.49      | ~ v1_relat_1(sK4)
% 7.87/1.49      | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4960]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4989,plain,
% 7.87/1.49      ( ~ v4_relat_1(sK4,k1_xboole_0)
% 7.87/1.49      | r1_tarski(sK1,k1_xboole_0)
% 7.87/1.49      | ~ v1_relat_1(sK4)
% 7.87/1.49      | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_4987]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5217,plain,
% 7.87/1.49      ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1052]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6317,plain,
% 7.87/1.49      ( ~ r1_tarski(sK1,X0) | ~ v1_relat_1(X0) | v1_relat_1(sK1) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_331]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6324,plain,
% 7.87/1.49      ( ~ r1_tarski(sK1,k1_xboole_0)
% 7.87/1.49      | v1_relat_1(sK1)
% 7.87/1.49      | ~ v1_relat_1(k1_xboole_0) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_6317]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1058,plain,
% 7.87/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.87/1.49      theory(equality) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6339,plain,
% 7.87/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(sK1) | sK1 != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1058]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6340,plain,
% 7.87/1.49      ( sK1 != X0
% 7.87/1.49      | v1_relat_1(X0) != iProver_top
% 7.87/1.49      | v1_relat_1(sK1) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_6339]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6342,plain,
% 7.87/1.49      ( sK1 != k1_xboole_0
% 7.87/1.49      | v1_relat_1(sK1) = iProver_top
% 7.87/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_6340]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1054,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.87/1.49      theory(equality) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4837,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,X1)
% 7.87/1.49      | r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
% 7.87/1.49      | k2_relset_1(sK1,sK2,sK4) != X1
% 7.87/1.49      | sK3 != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1054]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8125,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,k2_relset_1(sK1,sK2,sK4))
% 7.87/1.49      | r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
% 7.87/1.49      | k2_relset_1(sK1,sK2,sK4) != k2_relset_1(sK1,sK2,sK4)
% 7.87/1.49      | sK3 != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_4837]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8128,plain,
% 7.87/1.49      ( r1_tarski(sK3,k2_relset_1(sK1,sK2,sK4))
% 7.87/1.49      | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK4))
% 7.87/1.49      | k2_relset_1(sK1,sK2,sK4) != k2_relset_1(sK1,sK2,sK4)
% 7.87/1.49      | sK3 != k1_xboole_0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_8125]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8126,plain,
% 7.87/1.49      ( k2_relset_1(sK1,sK2,sK4) = k2_relset_1(sK1,sK2,sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1052]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_10,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1)
% 7.87/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.87/1.49      | ~ v1_relat_1(X0) ),
% 7.87/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1735,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5085,plain,
% 7.87/1.49      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1739,c_1735]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5297,plain,
% 7.87/1.49      ( r1_tarski(sK1,X0) = iProver_top
% 7.87/1.49      | v4_relat_1(sK4,X0) != iProver_top
% 7.87/1.49      | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_4960,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5298,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,X0) != iProver_top
% 7.87/1.49      | r1_tarski(sK1,X0) = iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_5297]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8302,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_5085,c_5298]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4909,plain,
% 7.87/1.49      ( k1_relset_1(sK1,sK3,sK4) != X0
% 7.87/1.49      | k1_relset_1(sK1,sK3,sK4) = sK1
% 7.87/1.49      | sK1 != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8048,plain,
% 7.87/1.49      ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(X0)
% 7.87/1.49      | k1_relset_1(sK1,sK3,sK4) = sK1
% 7.87/1.49      | sK1 != k1_relat_1(X0) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_4909]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_9486,plain,
% 7.87/1.49      ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
% 7.87/1.49      | k1_relset_1(sK1,sK3,sK4) = sK1
% 7.87/1.49      | sK1 != k1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_8048]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_9487,plain,
% 7.87/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.49      | k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_9827,plain,
% 7.87/1.49      ( r1_tarski(k1_xboole_0,k2_relset_1(sK1,sK2,sK4)) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2647,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,X1)
% 7.87/1.49      | r1_tarski(sK3,k1_xboole_0)
% 7.87/1.49      | sK3 != X0
% 7.87/1.49      | k1_xboole_0 != X1 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1054]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3030,plain,
% 7.87/1.49      ( ~ r1_tarski(sK3,X0)
% 7.87/1.49      | r1_tarski(sK3,k1_xboole_0)
% 7.87/1.49      | sK3 != sK3
% 7.87/1.49      | k1_xboole_0 != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2647]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_10834,plain,
% 7.87/1.49      ( ~ r1_tarski(sK3,sK3)
% 7.87/1.49      | r1_tarski(sK3,k1_xboole_0)
% 7.87/1.49      | sK3 != sK3
% 7.87/1.49      | k1_xboole_0 != sK3 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_3030]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_10835,plain,
% 7.87/1.49      ( r1_tarski(sK3,sK3) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8479,plain,
% 7.87/1.49      ( r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top
% 7.87/1.49      | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_8302,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8480,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_8479]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5088,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,X0) = iProver_top
% 7.87/1.49      | r1_tarski(sK1,X0) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4440,c_1735]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5308,plain,
% 7.87/1.49      ( r1_tarski(sK1,X0) != iProver_top
% 7.87/1.49      | v4_relat_1(sK4,X0) = iProver_top
% 7.87/1.49      | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_5088,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5309,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,X0) = iProver_top
% 7.87/1.49      | r1_tarski(sK1,X0) != iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_5308]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8488,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,k1_relat_1(sK4)) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_8480,c_5309]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4296,plain,
% 7.87/1.49      ( v4_relat_1(sK4,X0)
% 7.87/1.49      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 7.87/1.49      | ~ v1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5480,plain,
% 7.87/1.49      ( v4_relat_1(sK4,k1_relat_1(sK4))
% 7.87/1.49      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 7.87/1.49      | ~ v1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_4296]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5482,plain,
% 7.87/1.49      ( v4_relat_1(sK4,k1_relat_1(sK4)) = iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_5480]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5481,plain,
% 7.87/1.49      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5484,plain,
% 7.87/1.49      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_5481]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8502,plain,
% 7.87/1.49      ( v4_relat_1(sK4,k1_relat_1(sK4)) = iProver_top ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_8488,c_3808,c_5482,c_5484]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_15,plain,
% 7.87/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1730,plain,
% 7.87/1.49      ( k7_relat_1(X0,X1) = X0
% 7.87/1.49      | v4_relat_1(X0,X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8508,plain,
% 7.87/1.49      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_8502,c_1730]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8606,plain,
% 7.87/1.49      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_8508,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_13,plain,
% 7.87/1.49      ( ~ v1_relat_1(X0)
% 7.87/1.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.87/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1732,plain,
% 7.87/1.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3810,plain,
% 7.87/1.49      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3808,c_1732]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8614,plain,
% 7.87/1.49      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_8606,c_3810]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4050,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4,c_1726]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5601,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1739,c_4050]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_11933,plain,
% 7.87/1.49      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.87/1.49      | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
% 7.87/1.49      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3810,c_5601]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3070,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.87/1.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4,c_1729]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12354,plain,
% 7.87/1.49      ( v4_relat_1(k7_relat_1(sK4,X0),X1) = iProver_top
% 7.87/1.49      | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
% 7.87/1.49      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_11933,c_3070]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12944,plain,
% 7.87/1.49      ( v4_relat_1(k7_relat_1(sK4,k1_relat_1(sK4)),X0) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.49      | v1_relat_1(k7_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_8614,c_12354]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12948,plain,
% 7.87/1.49      ( v4_relat_1(sK4,X0) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(light_normalisation,[status(thm)],[c_12944,c_8606]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12956,plain,
% 7.87/1.49      ( v4_relat_1(sK4,X0)
% 7.87/1.49      | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0)
% 7.87/1.49      | ~ v1_relat_1(sK4) ),
% 7.87/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_12948]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12958,plain,
% 7.87/1.49      ( v4_relat_1(sK4,k1_xboole_0)
% 7.87/1.49      | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0)
% 7.87/1.49      | ~ v1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_12956]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2714,plain,
% 7.87/1.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3756,plain,
% 7.87/1.49      ( X0 != k2_relset_1(sK1,sK2,sK4)
% 7.87/1.49      | sK3 = X0
% 7.87/1.49      | sK3 != k2_relset_1(sK1,sK2,sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2714]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_19457,plain,
% 7.87/1.49      ( k2_relat_1(sK4) != k2_relset_1(sK1,sK2,sK4)
% 7.87/1.49      | sK3 != k2_relset_1(sK1,sK2,sK4)
% 7.87/1.49      | sK3 = k2_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_3756]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2166,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2374,plain,
% 7.87/1.49      ( ~ r1_tarski(k1_relat_1(X0),sK1)
% 7.87/1.49      | ~ r1_tarski(sK1,k1_relat_1(X0))
% 7.87/1.49      | sK1 = k1_relat_1(X0) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2166]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_27408,plain,
% 7.87/1.49      ( ~ r1_tarski(k1_relat_1(sK4),sK1)
% 7.87/1.49      | ~ r1_tarski(sK1,k1_relat_1(sK4))
% 7.87/1.49      | sK1 = k1_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2374]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_27409,plain,
% 7.87/1.49      ( sK1 = k1_relat_1(sK4)
% 7.87/1.49      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 7.87/1.49      | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_27408]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5222,plain,
% 7.87/1.49      ( X0 != X1 | k2_relat_1(sK4) != X1 | k2_relat_1(sK4) = X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_11823,plain,
% 7.87/1.49      ( X0 != k2_relat_1(sK4)
% 7.87/1.49      | k2_relat_1(sK4) = X0
% 7.87/1.49      | k2_relat_1(sK4) != k2_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_5222]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_33365,plain,
% 7.87/1.49      ( k2_relat_1(sK4) != k2_relat_1(sK4)
% 7.87/1.49      | k2_relat_1(sK4) = sK3
% 7.87/1.49      | sK3 != k2_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_11823]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_33378,plain,
% 7.87/1.49      ( k2_relset_1(sK1,sK2,sK4) != k2_relat_1(sK4)
% 7.87/1.49      | k2_relat_1(sK4) = k2_relset_1(sK1,sK2,sK4)
% 7.87/1.49      | k2_relat_1(sK4) != k2_relat_1(sK4) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_11823]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_33947,plain,
% 7.87/1.49      ( ~ v1_relat_1(sK1)
% 7.87/1.49      | k2_relset_1(k1_relat_1(k1_relat_1(sK4)),k2_relat_1(k1_relat_1(sK4)),k1_relat_1(sK4)) = k2_relat_1(k1_relat_1(sK4)) ),
% 7.87/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_33922]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6826,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,X1)
% 7.87/1.49      | r1_tarski(k2_relat_1(sK4),X2)
% 7.87/1.49      | X2 != X1
% 7.87/1.49      | k2_relat_1(sK4) != X0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_1054]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_34315,plain,
% 7.87/1.49      ( r1_tarski(k2_relat_1(sK4),X0)
% 7.87/1.49      | ~ r1_tarski(sK3,X1)
% 7.87/1.49      | X0 != X1
% 7.87/1.49      | k2_relat_1(sK4) != sK3 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_6826]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_34332,plain,
% 7.87/1.49      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0)
% 7.87/1.49      | ~ r1_tarski(sK3,k1_xboole_0)
% 7.87/1.49      | k2_relat_1(sK4) != sK3
% 7.87/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_34315]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_34913,plain,
% 7.87/1.49      ( k2_relset_1(k1_relat_1(k1_relat_1(sK4)),k2_relat_1(k1_relat_1(sK4)),k1_relat_1(sK4)) = k2_relat_1(k1_relat_1(sK4)) ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_33922,c_36,c_41,c_35,c_99,c_100,c_114,c_115,c_640,
% 7.87/1.49                 c_1982,c_1983,c_2029,c_2030,c_2076,c_2132,c_2133,c_2358,
% 7.87/1.49                 c_2423,c_2712,c_2713,c_2947,c_3698,c_3808,c_3809,c_4281,
% 7.87/1.49                 c_4282,c_4989,c_5217,c_6324,c_6342,c_8128,c_8126,c_8302,
% 7.87/1.49                 c_9486,c_9487,c_9827,c_10834,c_10835,c_12958,c_19457,
% 7.87/1.49                 c_27409,c_33365,c_33378,c_33947,c_34332]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_34916,plain,
% 7.87/1.49      ( k2_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) = k2_relat_1(k1_relat_1(sK4))
% 7.87/1.49      | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4440,c_34913]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4924,plain,
% 7.87/1.49      ( k7_relat_1(sK4,sK1) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3069,c_1730]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2393,plain,
% 7.87/1.49      ( ~ v4_relat_1(sK4,X0)
% 7.87/1.49      | ~ v1_relat_1(sK4)
% 7.87/1.49      | k7_relat_1(sK4,X0) = sK4 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4314,plain,
% 7.87/1.49      ( ~ v4_relat_1(sK4,sK1)
% 7.87/1.49      | ~ v1_relat_1(sK4)
% 7.87/1.49      | k7_relat_1(sK4,sK1) = sK4 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_2393]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5108,plain,
% 7.87/1.49      ( k7_relat_1(sK4,sK1) = sK4 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_4924,c_36,c_2029,c_3809,c_4314]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5111,plain,
% 7.87/1.49      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_5108,c_3810]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_14,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.87/1.49      | ~ v1_relat_1(X1)
% 7.87/1.49      | k9_relat_1(X1,X0) != k1_xboole_0
% 7.87/1.49      | k1_xboole_0 = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1731,plain,
% 7.87/1.49      ( k9_relat_1(X0,X1) != k1_xboole_0
% 7.87/1.49      | k1_xboole_0 = X1
% 7.87/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5431,plain,
% 7.87/1.49      ( k2_relat_1(sK4) != k1_xboole_0
% 7.87/1.49      | sK1 = k1_xboole_0
% 7.87/1.49      | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_5111,c_1731]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5434,plain,
% 7.87/1.49      ( r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top
% 7.87/1.49      | sK1 = k1_xboole_0
% 7.87/1.49      | k2_relat_1(sK4) != k1_xboole_0 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_5431,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5435,plain,
% 7.87/1.49      ( k2_relat_1(sK4) != k1_xboole_0
% 7.87/1.49      | sK1 = k1_xboole_0
% 7.87/1.49      | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_5434]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_6341,plain,
% 7.87/1.49      ( v1_relat_1(sK1)
% 7.87/1.49      | ~ v1_relat_1(k1_xboole_0)
% 7.87/1.49      | sK1 != k1_xboole_0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_6339]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_13069,plain,
% 7.87/1.49      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.49      | v4_relat_1(sK4,X0) = iProver_top ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_12948,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_13070,plain,
% 7.87/1.49      ( v4_relat_1(sK4,X0) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_13069]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_13071,plain,
% 7.87/1.49      ( v4_relat_1(sK4,X0) | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
% 7.87/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_13070]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_13073,plain,
% 7.87/1.49      ( v4_relat_1(sK4,k1_xboole_0)
% 7.87/1.49      | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_13071]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_17270,plain,
% 7.87/1.49      ( v1_relat_1(k1_relat_1(sK4))
% 7.87/1.49      | ~ v1_relat_1(sK1)
% 7.87/1.49      | ~ v1_relat_1(sK4) ),
% 7.87/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_17153]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1737,plain,
% 7.87/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.87/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3096,plain,
% 7.87/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.87/1.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1737,c_3070]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8166,plain,
% 7.87/1.49      ( v4_relat_1(X0,k1_xboole_0) != iProver_top
% 7.87/1.49      | v4_relat_1(k1_relat_1(X0),X1) = iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1734,c_3096]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4052,plain,
% 7.87/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1726,c_1736]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_9895,plain,
% 7.87/1.49      ( v4_relat_1(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(k1_relat_1(X0)),X2) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4052,c_1735]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_23694,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4440,c_9895]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_23968,plain,
% 7.87/1.49      ( v1_relat_1(k1_relat_1(sK4)) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) != iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.49      | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
% 7.87/1.49      | sK2 = k1_xboole_0 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_23694,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_23969,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.49      | r1_tarski(k1_relat_1(k1_relat_1(sK4)),X0) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_23968]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_23980,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(k1_relat_1(sK4),X0) != iProver_top
% 7.87/1.49      | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1734,c_23969]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1740,plain,
% 7.87/1.49      ( X0 = X1
% 7.87/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.87/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4961,plain,
% 7.87/1.49      ( k1_relat_1(X0) = X1
% 7.87/1.49      | v4_relat_1(X0,X1) != iProver_top
% 7.87/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.87/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1734,c_1740]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_11601,plain,
% 7.87/1.49      ( k1_relat_1(sK4) = X0
% 7.87/1.49      | sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,X0) != iProver_top
% 7.87/1.49      | r1_tarski(X0,sK1) != iProver_top
% 7.87/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4440,c_4961]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12093,plain,
% 7.87/1.49      ( r1_tarski(X0,sK1) != iProver_top
% 7.87/1.49      | v4_relat_1(sK4,X0) != iProver_top
% 7.87/1.49      | sK2 = k1_xboole_0
% 7.87/1.49      | k1_relat_1(sK4) = X0 ),
% 7.87/1.49      inference(global_propositional_subsumption,
% 7.87/1.49                [status(thm)],
% 7.87/1.49                [c_11601,c_3808]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12094,plain,
% 7.87/1.49      ( k1_relat_1(sK4) = X0
% 7.87/1.49      | sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(sK4,X0) != iProver_top
% 7.87/1.49      | r1_tarski(X0,sK1) != iProver_top ),
% 7.87/1.49      inference(renaming,[status(thm)],[c_12093]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_26910,plain,
% 7.87/1.49      ( k2_zfmisc_1(X0,X1) = k1_relat_1(sK4)
% 7.87/1.49      | sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(k1_relat_1(sK4),X0) != iProver_top
% 7.87/1.49      | r1_tarski(k2_zfmisc_1(X0,X1),sK1) != iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_23980,c_12094]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_29251,plain,
% 7.87/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_relat_1(sK4)
% 7.87/1.49      | sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.49      | r1_tarski(k1_xboole_0,sK1) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_5,c_26910]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_29258,plain,
% 7.87/1.49      ( k1_relat_1(sK4) = k1_xboole_0
% 7.87/1.49      | sK2 = k1_xboole_0
% 7.87/1.49      | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.49      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.49      | r1_tarski(k1_xboole_0,sK1) != iProver_top
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.49      inference(light_normalisation,[status(thm)],[c_29251,c_5]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8487,plain,
% 7.87/1.49      ( sK2 = k1_xboole_0
% 7.87/1.49      | v1_relat_1(k1_relat_1(sK4)) != iProver_top
% 7.87/1.49      | v1_relat_1(sK1) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_8480,c_1720]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_8653,plain,
% 7.87/1.49      ( v1_relat_1(k1_relat_1(sK4)) != iProver_top
% 7.87/1.49      | v1_relat_1(sK1) = iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_8487,c_100,c_1983,c_2133,c_2358,c_6342]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3067,plain,
% 7.87/1.50      ( v4_relat_1(X0,X1) = iProver_top
% 7.87/1.50      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1737,c_1729]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_7061,plain,
% 7.87/1.50      ( v4_relat_1(X0,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_3067]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_7250,plain,
% 7.87/1.50      ( v4_relat_1(X0,k1_xboole_0) != iProver_top
% 7.87/1.50      | v4_relat_1(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1734,c_7061]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_11067,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK1,k1_xboole_0) = iProver_top
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4440,c_7250]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_26906,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_23980]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_86,plain,
% 7.87/1.50      ( v4_relat_1(X0,X1) = iProver_top
% 7.87/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_88,plain,
% 7.87/1.50      ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 7.87/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_86]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_116,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_118,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_116]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2023,plain,
% 7.87/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2024,plain,
% 7.87/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.87/1.50      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2023]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2026,plain,
% 7.87/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2024]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2161,plain,
% 7.87/1.50      ( ~ r1_tarski(X0,X1)
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0)
% 7.87/1.50      | sK1 != X0
% 7.87/1.50      | k1_xboole_0 != X1 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1054]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2162,plain,
% 7.87/1.50      ( sK1 != X0
% 7.87/1.50      | k1_xboole_0 != X1
% 7.87/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2164,plain,
% 7.87/1.50      ( sK1 != k1_xboole_0
% 7.87/1.50      | k1_xboole_0 != k1_xboole_0
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2162]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1059,plain,
% 7.87/1.50      ( ~ v4_relat_1(X0,X1) | v4_relat_1(X2,X1) | X2 != X0 ),
% 7.87/1.50      theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4309,plain,
% 7.87/1.50      ( ~ v4_relat_1(X0,X1) | v4_relat_1(sK4,X1) | sK4 != X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1059]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4310,plain,
% 7.87/1.50      ( sK4 != X0
% 7.87/1.50      | v4_relat_1(X0,X1) != iProver_top
% 7.87/1.50      | v4_relat_1(sK4,X1) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_4309]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4312,plain,
% 7.87/1.50      ( sK4 != k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_4310]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9893,plain,
% 7.87/1.50      ( k2_zfmisc_1(X0,X1) = X2
% 7.87/1.50      | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 7.87/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4052,c_1740]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22243,plain,
% 7.87/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 7.87/1.50      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(X1),k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 7.87/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_9893]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22249,plain,
% 7.87/1.50      ( k1_xboole_0 = X0
% 7.87/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_22243,c_5]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1738,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4855,plain,
% 7.87/1.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1738,c_1740]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9892,plain,
% 7.87/1.50      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_4052]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10039,plain,
% 7.87/1.50      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1739,c_9892]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22490,plain,
% 7.87/1.50      ( r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 7.87/1.50      | k1_xboole_0 = X0
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_22249,c_4855,c_10039]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22491,plain,
% 7.87/1.50      ( k1_xboole_0 = X0
% 7.87/1.50      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_22490]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22500,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | sK4 = k1_xboole_0
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4440,c_22491]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2151,plain,
% 7.87/1.50      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2152,plain,
% 7.87/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.87/1.50      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2151]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2704,plain,
% 7.87/1.50      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
% 7.87/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2690]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2232,plain,
% 7.87/1.50      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2773,plain,
% 7.87/1.50      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2232]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2774,plain,
% 7.87/1.50      ( r1_tarski(sK4,sK4) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2780,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,sK4) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2921,plain,
% 7.87/1.50      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2923,plain,
% 7.87/1.50      ( ~ r1_tarski(sK4,k1_xboole_0)
% 7.87/1.50      | ~ r1_tarski(k1_xboole_0,sK4)
% 7.87/1.50      | sK4 = k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2921]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2913,plain,
% 7.87/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1054]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4636,plain,
% 7.87/1.50      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) | X1 != X0 | sK4 != sK4 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2913]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6881,plain,
% 7.87/1.50      ( r1_tarski(sK4,X0)
% 7.87/1.50      | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 7.87/1.50      | X0 != k2_zfmisc_1(sK1,sK2)
% 7.87/1.50      | sK4 != sK4 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_4636]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6883,plain,
% 7.87/1.50      ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 7.87/1.50      | r1_tarski(sK4,k1_xboole_0)
% 7.87/1.50      | sK4 != sK4
% 7.87/1.50      | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_6881]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1055,plain,
% 7.87/1.50      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.87/1.50      theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9571,plain,
% 7.87/1.50      ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(X0,X1)
% 7.87/1.50      | sK2 != X1
% 7.87/1.50      | sK1 != X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1055]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9573,plain,
% 7.87/1.50      ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | sK2 != k1_xboole_0
% 7.87/1.50      | sK1 != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_9571]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_8108,plain,
% 7.87/1.50      ( X0 != X1
% 7.87/1.50      | X0 = k2_zfmisc_1(sK1,sK2)
% 7.87/1.50      | k2_zfmisc_1(sK1,sK2) != X1 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2151]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22352,plain,
% 7.87/1.50      ( X0 != k2_zfmisc_1(X1,X2)
% 7.87/1.50      | X0 = k2_zfmisc_1(sK1,sK2)
% 7.87/1.50      | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(X1,X2) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_8108]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22354,plain,
% 7.87/1.50      ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
% 7.87/1.50      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_22352]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22918,plain,
% 7.87/1.50      ( r1_tarski(sK1,k1_xboole_0) != iProver_top | sK4 = k1_xboole_0 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_22500,c_114,c_115,c_2152,c_2358,c_2704,c_2773,c_2774,
% 7.87/1.50                 c_2780,c_2923,c_3808,c_6883,c_9573,c_22354]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22919,plain,
% 7.87/1.50      ( sK4 = k1_xboole_0 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_22918]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_26911,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(k1_relat_1(sK4),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.50      | r1_tarski(sK1,k2_zfmisc_1(X0,X1)) = iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_23980,c_5298]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_27166,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_26911]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_27648,plain,
% 7.87/1.50      ( v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_26906,c_88,c_114,c_115,c_117,c_2026,c_2133,c_2163,
% 7.87/1.50                 c_2358,c_4312,c_22920]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_27656,plain,
% 7.87/1.50      ( v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1739,c_27648]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_23982,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4440,c_23969]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_24231,plain,
% 7.87/1.50      ( k2_zfmisc_1(X0,X1) = k1_relat_1(sK4)
% 7.87/1.50      | sK2 = k1_xboole_0
% 7.87/1.50      | r1_tarski(k2_zfmisc_1(X0,X1),sK1) != iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_23982,c_12094]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_28661,plain,
% 7.87/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_relat_1(sK4)
% 7.87/1.50      | sK2 = k1_xboole_0
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,sK1) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_24231]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_28668,plain,
% 7.87/1.50      ( k1_relat_1(sK4) = k1_xboole_0
% 7.87/1.50      | sK2 = k1_xboole_0
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,sK1) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_28661,c_5]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_28,plain,
% 7.87/1.50      ( v1_funct_2(sK0(X0,X1),X0,X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_663,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.50      | sK0(X0,X1) != sK4
% 7.87/1.50      | sK3 != X1
% 7.87/1.50      | sK1 != X0 ),
% 7.87/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_196]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_664,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.50      | sK0(sK1,sK3) != sK4 ),
% 7.87/1.50      inference(unflattening,[status(thm)],[c_663]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2202,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,sK0(X0,X1)) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2205,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,sK0(X0,X1)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2202]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2207,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2205]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22,plain,
% 7.87/1.50      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.87/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.87/1.50      | k1_xboole_0 = X0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_529,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.87/1.50      | sK3 != k1_xboole_0
% 7.87/1.50      | sK1 != X0
% 7.87/1.50      | sK4 != k1_xboole_0
% 7.87/1.50      | k1_xboole_0 = X0 ),
% 7.87/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_196]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_530,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.87/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 7.87/1.50      | sK3 != k1_xboole_0
% 7.87/1.50      | sK4 != k1_xboole_0
% 7.87/1.50      | k1_xboole_0 = sK1 ),
% 7.87/1.50      inference(unflattening,[status(thm)],[c_529]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1719,plain,
% 7.87/1.50      ( sK3 != k1_xboole_0
% 7.87/1.50      | sK4 != k1_xboole_0
% 7.87/1.50      | k1_xboole_0 = sK1
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.87/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1898,plain,
% 7.87/1.50      ( sK3 != k1_xboole_0
% 7.87/1.50      | sK1 = k1_xboole_0
% 7.87/1.50      | sK4 != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.87/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_1719,c_4]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_111,plain,
% 7.87/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.87/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_113,plain,
% 7.87/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_111]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2349,plain,
% 7.87/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.87/1.50      | sK4 != k1_xboole_0
% 7.87/1.50      | sK1 = k1_xboole_0
% 7.87/1.50      | sK3 != k1_xboole_0 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_1898,c_113,c_118]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2350,plain,
% 7.87/1.50      ( sK3 != k1_xboole_0
% 7.87/1.50      | sK1 = k1_xboole_0
% 7.87/1.50      | sK4 != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_2349]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2424,plain,
% 7.87/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 7.87/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2423]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_32,plain,
% 7.87/1.50      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.87/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1723,plain,
% 7.87/1.50      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2598,plain,
% 7.87/1.50      ( m1_subset_1(sK0(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4,c_1723]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2691,plain,
% 7.87/1.50      ( r1_tarski(sK0(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2598,c_1736]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4859,plain,
% 7.87/1.50      ( sK0(X0,k1_xboole_0) = k1_xboole_0
% 7.87/1.50      | r1_tarski(k1_xboole_0,sK0(X0,k1_xboole_0)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2691,c_1740]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4892,plain,
% 7.87/1.50      ( sK0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 7.87/1.50      | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_4859]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2927,plain,
% 7.87/1.50      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_11529,plain,
% 7.87/1.50      ( sK0(X0,X1) != X2 | sK4 != X2 | sK4 = sK0(X0,X1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2927]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_11530,plain,
% 7.87/1.50      ( sK0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.87/1.50      | sK4 = sK0(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | sK4 != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_11529]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2245,plain,
% 7.87/1.50      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9666,plain,
% 7.87/1.50      ( sK0(sK1,sK3) != X0 | sK0(sK1,sK3) = sK4 | sK4 != X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2245]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_18747,plain,
% 7.87/1.50      ( sK0(sK1,sK3) != sK0(X0,X1)
% 7.87/1.50      | sK0(sK1,sK3) = sK4
% 7.87/1.50      | sK4 != sK0(X0,X1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_9666]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_18749,plain,
% 7.87/1.50      ( sK0(sK1,sK3) != sK0(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | sK0(sK1,sK3) = sK4
% 7.87/1.50      | sK4 != sK0(k1_xboole_0,k1_xboole_0) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_18747]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1064,plain,
% 7.87/1.50      ( X0 != X1 | X2 != X3 | sK0(X0,X2) = sK0(X1,X3) ),
% 7.87/1.50      theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_18748,plain,
% 7.87/1.50      ( sK0(sK1,sK3) = sK0(X0,X1) | sK3 != X1 | sK1 != X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1064]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_18750,plain,
% 7.87/1.50      ( sK0(sK1,sK3) = sK0(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | sK3 != k1_xboole_0
% 7.87/1.50      | sK1 != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_18748]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_24232,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
% 7.87/1.50      | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) = iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_23982,c_5298]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_27068,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_24232]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4988,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.87/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_4960]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_24228,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_23982]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9897,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4052,c_5309]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10426,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_9897]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_8109,plain,
% 7.87/1.50      ( k2_zfmisc_1(sK1,sK2) != k1_xboole_0
% 7.87/1.50      | k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
% 7.87/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_8108]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_8275,plain,
% 7.87/1.50      ( k2_zfmisc_1(sK1,sK2) != X0
% 7.87/1.50      | k2_zfmisc_1(sK1,sK2) = k1_xboole_0
% 7.87/1.50      | k1_xboole_0 != X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1053]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9570,plain,
% 7.87/1.50      ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(X0,X1)
% 7.87/1.50      | k2_zfmisc_1(sK1,sK2) = k1_xboole_0
% 7.87/1.50      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_8275]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9572,plain,
% 7.87/1.50      ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | k2_zfmisc_1(sK1,sK2) = k1_xboole_0
% 7.87/1.50      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_9570]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10533,plain,
% 7.87/1.50      ( v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_10426,c_88,c_114,c_115,c_2026,c_2133,c_2152,c_2358,
% 7.87/1.50                 c_2704,c_2773,c_2774,c_2780,c_2923,c_4312,c_6883,c_8109,
% 7.87/1.50                 c_9572,c_9573]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10541,plain,
% 7.87/1.50      ( v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1739,c_10533]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_24841,plain,
% 7.87/1.50      ( v4_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_24228,c_8653,c_10541]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_27684,plain,
% 7.87/1.50      ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_27068,c_114,c_115,c_118,c_2164,c_2358,c_3808,c_4988,
% 7.87/1.50                 c_24841]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_28968,plain,
% 7.87/1.50      ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | sK2 = k1_xboole_0
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_28668,c_36,c_41,c_114,c_115,c_640,c_664,c_2029,c_2030,
% 7.87/1.50                 c_2152,c_2207,c_2350,c_2358,c_2423,c_2424,c_2704,c_2712,
% 7.87/1.50                 c_2713,c_2773,c_2774,c_2780,c_2923,c_3697,c_3698,c_3808,
% 7.87/1.50                 c_3809,c_4281,c_4282,c_4892,c_6883,c_8302,c_9486,c_9487,
% 7.87/1.50                 c_9573,c_11530,c_18749,c_18750,c_22354,c_22500,c_27409,
% 7.87/1.50                 c_27684]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_28969,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_28968]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_28975,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK1,k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top
% 7.87/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1734,c_28969]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_30441,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_29258,c_3808,c_8653,c_11067,c_27656,c_28975]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_30448,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0
% 7.87/1.50      | v4_relat_1(sK4,k1_xboole_0) != iProver_top
% 7.87/1.50      | v1_relat_1(k1_relat_1(sK4)) != iProver_top
% 7.87/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_8166,c_30441]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_30466,plain,
% 7.87/1.50      ( ~ v4_relat_1(sK4,k1_xboole_0)
% 7.87/1.50      | ~ v1_relat_1(k1_relat_1(sK4))
% 7.87/1.50      | ~ v1_relat_1(sK4)
% 7.87/1.50      | sK2 = k1_xboole_0 ),
% 7.87/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_30448]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35165,plain,
% 7.87/1.50      ( X0 != sK3 | k2_relat_1(sK4) = X0 | k2_relat_1(sK4) != sK3 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_5222]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35167,plain,
% 7.87/1.50      ( k2_relat_1(sK4) != sK3
% 7.87/1.50      | k2_relat_1(sK4) = k1_xboole_0
% 7.87/1.50      | k1_xboole_0 != sK3 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_35165]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35705,plain,
% 7.87/1.50      ( sK2 = k1_xboole_0 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_34916,c_36,c_41,c_35,c_99,c_114,c_115,c_640,c_1982,
% 7.87/1.50                 c_2029,c_2030,c_2076,c_2132,c_2423,c_2712,c_2713,c_2947,
% 7.87/1.50                 c_3698,c_3808,c_3809,c_4281,c_4282,c_5217,c_5435,c_6341,
% 7.87/1.50                 c_8128,c_8126,c_8302,c_9486,c_9487,c_9827,c_10834,
% 7.87/1.50                 c_10835,c_13073,c_17270,c_19457,c_27409,c_30466,c_33365,
% 7.87/1.50                 c_33378,c_34332,c_35167]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35796,plain,
% 7.87/1.50      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_35705,c_34]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35797,plain,
% 7.87/1.50      ( sK1 = k1_xboole_0 ),
% 7.87/1.50      inference(equality_resolution_simp,[status(thm)],[c_35796]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1714,plain,
% 7.87/1.50      ( sK0(sK1,sK3) != sK4
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35890,plain,
% 7.87/1.50      ( sK0(k1_xboole_0,sK3) != sK4
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_35797,c_1714]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2599,plain,
% 7.87/1.50      ( m1_subset_1(sK0(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5,c_1723]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2692,plain,
% 7.87/1.50      ( r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2599,c_1736]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5578,plain,
% 7.87/1.50      ( sK0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2692,c_4855]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35893,plain,
% 7.87/1.50      ( sK4 != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_35890,c_5,c_5578]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22920,plain,
% 7.87/1.50      ( ~ r1_tarski(sK1,k1_xboole_0) | sK4 = k1_xboole_0 ),
% 7.87/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_22919]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1057,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.87/1.50      theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2087,plain,
% 7.87/1.50      ( m1_subset_1(X0,X1)
% 7.87/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.87/1.50      | X0 != X2
% 7.87/1.50      | X1 != k1_zfmisc_1(X3) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1057]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2521,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.87/1.50      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.87/1.50      | X2 != X0
% 7.87/1.50      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2087]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4370,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(X2))
% 7.87/1.50      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
% 7.87/1.50      | sK4 != X0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2521]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4371,plain,
% 7.87/1.50      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 7.87/1.50      | sK4 != X2
% 7.87/1.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_4370]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4373,plain,
% 7.87/1.50      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 7.87/1.50      | sK4 != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.87/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_4371]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2163,plain,
% 7.87/1.50      ( r1_tarski(sK1,k1_xboole_0)
% 7.87/1.50      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.87/1.50      | sK1 != k1_xboole_0
% 7.87/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2161]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1056,plain,
% 7.87/1.50      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.87/1.50      theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1067,plain,
% 7.87/1.50      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 7.87/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1056]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_117,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(contradiction,plain,
% 7.87/1.50      ( $false ),
% 7.87/1.50      inference(minisat,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_35893,c_35705,c_22920,c_4373,c_2358,c_2163,c_1067,
% 7.87/1.50                 c_118,c_117,c_115,c_114,c_113]) ).
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.50  
% 7.87/1.50  ------                               Statistics
% 7.87/1.50  
% 7.87/1.50  ------ General
% 7.87/1.50  
% 7.87/1.50  abstr_ref_over_cycles:                  0
% 7.87/1.50  abstr_ref_under_cycles:                 0
% 7.87/1.50  gc_basic_clause_elim:                   0
% 7.87/1.50  forced_gc_time:                         0
% 7.87/1.50  parsing_time:                           0.011
% 7.87/1.50  unif_index_cands_time:                  0.
% 7.87/1.50  unif_index_add_time:                    0.
% 7.87/1.50  orderings_time:                         0.
% 7.87/1.50  out_proof_time:                         0.028
% 7.87/1.50  total_time:                             0.883
% 7.87/1.50  num_of_symbols:                         51
% 7.87/1.50  num_of_terms:                           22351
% 7.87/1.50  
% 7.87/1.50  ------ Preprocessing
% 7.87/1.50  
% 7.87/1.50  num_of_splits:                          0
% 7.87/1.50  num_of_split_atoms:                     0
% 7.87/1.50  num_of_reused_defs:                     0
% 7.87/1.50  num_eq_ax_congr_red:                    19
% 7.87/1.50  num_of_sem_filtered_clauses:            3
% 7.87/1.50  num_of_subtypes:                        0
% 7.87/1.50  monotx_restored_types:                  0
% 7.87/1.50  sat_num_of_epr_types:                   0
% 7.87/1.50  sat_num_of_non_cyclic_types:            0
% 7.87/1.50  sat_guarded_non_collapsed_types:        0
% 7.87/1.50  num_pure_diseq_elim:                    0
% 7.87/1.50  simp_replaced_by:                       0
% 7.87/1.50  res_preprocessed:                       179
% 7.87/1.50  prep_upred:                             0
% 7.87/1.50  prep_unflattend:                        52
% 7.87/1.50  smt_new_axioms:                         0
% 7.87/1.50  pred_elim_cands:                        4
% 7.87/1.50  pred_elim:                              1
% 7.87/1.50  pred_elim_cl:                           -2
% 7.87/1.50  pred_elim_cycles:                       4
% 7.87/1.50  merged_defs:                            8
% 7.87/1.50  merged_defs_ncl:                        0
% 7.87/1.50  bin_hyper_res:                          9
% 7.87/1.50  prep_cycles:                            4
% 7.87/1.50  pred_elim_time:                         0.007
% 7.87/1.50  splitting_time:                         0.
% 7.87/1.50  sem_filter_time:                        0.
% 7.87/1.50  monotx_time:                            0.
% 7.87/1.50  subtype_inf_time:                       0.
% 7.87/1.50  
% 7.87/1.50  ------ Problem properties
% 7.87/1.50  
% 7.87/1.50  clauses:                                38
% 7.87/1.50  conjectures:                            3
% 7.87/1.50  epr:                                    5
% 7.87/1.50  horn:                                   33
% 7.87/1.50  ground:                                 13
% 7.87/1.50  unary:                                  13
% 7.87/1.50  binary:                                 12
% 7.87/1.50  lits:                                   82
% 7.87/1.50  lits_eq:                                37
% 7.87/1.50  fd_pure:                                0
% 7.87/1.50  fd_pseudo:                              0
% 7.87/1.50  fd_cond:                                3
% 7.87/1.50  fd_pseudo_cond:                         1
% 7.87/1.50  ac_symbols:                             0
% 7.87/1.50  
% 7.87/1.50  ------ Propositional Solver
% 7.87/1.50  
% 7.87/1.50  prop_solver_calls:                      32
% 7.87/1.50  prop_fast_solver_calls:                 2762
% 7.87/1.50  smt_solver_calls:                       0
% 7.87/1.50  smt_fast_solver_calls:                  0
% 7.87/1.50  prop_num_of_clauses:                    11790
% 7.87/1.50  prop_preprocess_simplified:             17832
% 7.87/1.50  prop_fo_subsumed:                       140
% 7.87/1.50  prop_solver_time:                       0.
% 7.87/1.50  smt_solver_time:                        0.
% 7.87/1.50  smt_fast_solver_time:                   0.
% 7.87/1.50  prop_fast_solver_time:                  0.
% 7.87/1.50  prop_unsat_core_time:                   0.001
% 7.87/1.50  
% 7.87/1.50  ------ QBF
% 7.87/1.50  
% 7.87/1.50  qbf_q_res:                              0
% 7.87/1.50  qbf_num_tautologies:                    0
% 7.87/1.50  qbf_prep_cycles:                        0
% 7.87/1.50  
% 7.87/1.50  ------ BMC1
% 7.87/1.50  
% 7.87/1.50  bmc1_current_bound:                     -1
% 7.87/1.50  bmc1_last_solved_bound:                 -1
% 7.87/1.50  bmc1_unsat_core_size:                   -1
% 7.87/1.50  bmc1_unsat_core_parents_size:           -1
% 7.87/1.50  bmc1_merge_next_fun:                    0
% 7.87/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.87/1.50  
% 7.87/1.50  ------ Instantiation
% 7.87/1.50  
% 7.87/1.50  inst_num_of_clauses:                    3312
% 7.87/1.50  inst_num_in_passive:                    445
% 7.87/1.50  inst_num_in_active:                     1329
% 7.87/1.50  inst_num_in_unprocessed:                1541
% 7.87/1.50  inst_num_of_loops:                      2050
% 7.87/1.50  inst_num_of_learning_restarts:          0
% 7.87/1.50  inst_num_moves_active_passive:          716
% 7.87/1.50  inst_lit_activity:                      0
% 7.87/1.50  inst_lit_activity_moves:                0
% 7.87/1.50  inst_num_tautologies:                   0
% 7.87/1.50  inst_num_prop_implied:                  0
% 7.87/1.50  inst_num_existing_simplified:           0
% 7.87/1.50  inst_num_eq_res_simplified:             0
% 7.87/1.50  inst_num_child_elim:                    0
% 7.87/1.50  inst_num_of_dismatching_blockings:      1634
% 7.87/1.50  inst_num_of_non_proper_insts:           4141
% 7.87/1.50  inst_num_of_duplicates:                 0
% 7.87/1.50  inst_inst_num_from_inst_to_res:         0
% 7.87/1.50  inst_dismatching_checking_time:         0.
% 7.87/1.50  
% 7.87/1.50  ------ Resolution
% 7.87/1.50  
% 7.87/1.50  res_num_of_clauses:                     0
% 7.87/1.50  res_num_in_passive:                     0
% 7.87/1.50  res_num_in_active:                      0
% 7.87/1.50  res_num_of_loops:                       183
% 7.87/1.50  res_forward_subset_subsumed:            157
% 7.87/1.50  res_backward_subset_subsumed:           16
% 7.87/1.50  res_forward_subsumed:                   0
% 7.87/1.50  res_backward_subsumed:                  0
% 7.87/1.50  res_forward_subsumption_resolution:     2
% 7.87/1.50  res_backward_subsumption_resolution:    0
% 7.87/1.50  res_clause_to_clause_subsumption:       6960
% 7.87/1.50  res_orphan_elimination:                 0
% 7.87/1.50  res_tautology_del:                      294
% 7.87/1.50  res_num_eq_res_simplified:              1
% 7.87/1.50  res_num_sel_changes:                    0
% 7.87/1.50  res_moves_from_active_to_pass:          0
% 7.87/1.50  
% 7.87/1.50  ------ Superposition
% 7.87/1.50  
% 7.87/1.50  sup_time_total:                         0.
% 7.87/1.50  sup_time_generating:                    0.
% 7.87/1.50  sup_time_sim_full:                      0.
% 7.87/1.50  sup_time_sim_immed:                     0.
% 7.87/1.50  
% 7.87/1.50  sup_num_of_clauses:                     525
% 7.87/1.50  sup_num_in_active:                      190
% 7.87/1.50  sup_num_in_passive:                     335
% 7.87/1.50  sup_num_of_loops:                       409
% 7.87/1.50  sup_fw_superposition:                   1005
% 7.87/1.50  sup_bw_superposition:                   336
% 7.87/1.50  sup_immediate_simplified:               477
% 7.87/1.50  sup_given_eliminated:                   20
% 7.87/1.50  comparisons_done:                       0
% 7.87/1.50  comparisons_avoided:                    274
% 7.87/1.50  
% 7.87/1.50  ------ Simplifications
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  sim_fw_subset_subsumed:                 81
% 7.87/1.50  sim_bw_subset_subsumed:                 99
% 7.87/1.50  sim_fw_subsumed:                        136
% 7.87/1.50  sim_bw_subsumed:                        62
% 7.87/1.50  sim_fw_subsumption_res:                 10
% 7.87/1.50  sim_bw_subsumption_res:                 0
% 7.87/1.50  sim_tautology_del:                      44
% 7.87/1.50  sim_eq_tautology_del:                   247
% 7.87/1.50  sim_eq_res_simp:                        5
% 7.87/1.50  sim_fw_demodulated:                     145
% 7.87/1.50  sim_bw_demodulated:                     148
% 7.87/1.50  sim_light_normalised:                   252
% 7.87/1.50  sim_joinable_taut:                      0
% 7.87/1.50  sim_joinable_simp:                      0
% 7.87/1.50  sim_ac_normalised:                      0
% 7.87/1.50  sim_smt_subsumption:                    0
% 7.87/1.50  
%------------------------------------------------------------------------------
