%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:36 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  153 (2865 expanded)
%              Number of clauses        :  111 (1053 expanded)
%              Number of leaves         :   10 ( 532 expanded)
%              Depth                    :   28
%              Number of atoms          :  579 (18326 expanded)
%              Number of equality atoms :  346 (5871 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f19,plain,
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
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f30])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f39,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f29])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f26])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_relset_1(k1_xboole_0,X1,X2) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f28])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_296,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_297,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_1060,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK1 != X1
    | sK0 != X0
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_297])).

cnf(c_1061,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1060])).

cnf(c_1409,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_1061])).

cnf(c_1854,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1409])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_341,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_342,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_1427,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(X0_44,X1_44,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_342])).

cnf(c_2146,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1427])).

cnf(c_2227,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1854,c_2146])).

cnf(c_4,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_434,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_13,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_100,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_18])).

cnf(c_101,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_100])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_217,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_218,c_18])).

cnf(c_246,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_600,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_101,c_246])).

cnf(c_772,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK2 != k1_xboole_0
    | sK0 != X0
    | sK3 != sK3
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_434,c_600])).

cnf(c_773,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_1422,plain,
    ( ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_773])).

cnf(c_1807,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1422])).

cnf(c_11,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_199,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_200,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_258,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),sK2)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_200,c_18])).

cnf(c_259,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_872,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relat_1(sK3) != sK0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_600,c_259])).

cnf(c_1418,plain,
    ( ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relat_1(sK3) != sK0
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(subtyping,[status(esa)],[c_872])).

cnf(c_1529,plain,
    ( ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relat_1(sK3) != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1418])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_332,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_333,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_1428,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_relset_1(X0_44,X1_44,sK3) = k2_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_2149,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1428])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_279,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_280,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_1429,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_280])).

cnf(c_1800,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_44)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_2234,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1800])).

cnf(c_2235,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2234])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1431,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2239,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_492,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
    | sK3 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_246])).

cnf(c_493,plain,
    ( ~ v1_funct_2(sK3,X0,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_1071,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | sK1 != k1_xboole_0
    | sK0 != X0
    | sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_493])).

cnf(c_1072,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
    | sK1 != k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_1071])).

cnf(c_1408,plain,
    ( ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | sK1 != k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_1072])).

cnf(c_1816,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | sK1 != k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1408])).

cnf(c_1437,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1458,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1430,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1440,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_2265,plain,
    ( X0_44 != X1_44
    | X0_44 = sK1
    | sK1 != X1_44 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_2266,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2265])).

cnf(c_2372,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1816,c_1458,c_1430,c_2266])).

cnf(c_2373,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(renaming,[status(thm)],[c_2372])).

cnf(c_2578,plain,
    ( k1_xboole_0 = sK0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1807,c_1529,c_2149,c_2227,c_2235,c_2239,c_2373])).

cnf(c_2579,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_xboole_0 = sK0 ),
    inference(renaming,[status(thm)],[c_2578])).

cnf(c_2582,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2227,c_2579])).

cnf(c_2173,plain,
    ( sK0 != X0_44
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_44 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_2185,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_2186,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_2879,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_2185,c_2186,c_2373])).

cnf(c_2901,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2879,c_2146])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_516,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_517,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_1126,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK1 != X0
    | sK0 != k1_xboole_0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_517])).

cnf(c_1127,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1126])).

cnf(c_1405,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1127])).

cnf(c_2903,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2879,c_1405])).

cnf(c_2915,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2903])).

cnf(c_2918,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2901,c_2915])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_246])).

cnf(c_547,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_1187,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | sK2 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_547])).

cnf(c_1188,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) ),
    inference(unflattening,[status(thm)],[c_1187])).

cnf(c_1402,plain,
    ( ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1188])).

cnf(c_1820,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_2665,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_1402,c_2149,c_2235,c_2239])).

cnf(c_2666,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2665])).

cnf(c_3107,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2918,c_2666])).

cnf(c_3118,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3107])).

cnf(c_6,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_567,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_246])).

cnf(c_568,plain,
    ( v1_funct_2(sK3,k1_xboole_0,X0)
    | ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,X0,sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_961,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,X0,sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | sK2 != X0
    | sK0 != k1_xboole_0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_600,c_568])).

cnf(c_962,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_1414,plain,
    ( ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_962])).

cnf(c_1812,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1414])).

cnf(c_2758,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1812,c_1414,c_2149,c_2185,c_2186,c_2235,c_2239,c_2373,c_2582])).

cnf(c_2759,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2758])).

cnf(c_2884,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2879,c_2759])).

cnf(c_2952,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2884,c_2918])).

cnf(c_2953,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2952])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3118,c_2953])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:40:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.56/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/0.99  
% 1.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.56/0.99  
% 1.56/0.99  ------  iProver source info
% 1.56/0.99  
% 1.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.56/0.99  git: non_committed_changes: false
% 1.56/0.99  git: last_make_outside_of_git: false
% 1.56/0.99  
% 1.56/0.99  ------ 
% 1.56/0.99  
% 1.56/0.99  ------ Input Options
% 1.56/0.99  
% 1.56/0.99  --out_options                           all
% 1.56/0.99  --tptp_safe_out                         true
% 1.56/0.99  --problem_path                          ""
% 1.56/0.99  --include_path                          ""
% 1.56/0.99  --clausifier                            res/vclausify_rel
% 1.56/0.99  --clausifier_options                    --mode clausify
% 1.56/0.99  --stdin                                 false
% 1.56/0.99  --stats_out                             all
% 1.56/0.99  
% 1.56/0.99  ------ General Options
% 1.56/0.99  
% 1.56/0.99  --fof                                   false
% 1.56/0.99  --time_out_real                         305.
% 1.56/0.99  --time_out_virtual                      -1.
% 1.56/0.99  --symbol_type_check                     false
% 1.56/0.99  --clausify_out                          false
% 1.56/0.99  --sig_cnt_out                           false
% 1.56/0.99  --trig_cnt_out                          false
% 1.56/0.99  --trig_cnt_out_tolerance                1.
% 1.56/0.99  --trig_cnt_out_sk_spl                   false
% 1.56/0.99  --abstr_cl_out                          false
% 1.56/0.99  
% 1.56/0.99  ------ Global Options
% 1.56/0.99  
% 1.56/0.99  --schedule                              default
% 1.56/0.99  --add_important_lit                     false
% 1.56/0.99  --prop_solver_per_cl                    1000
% 1.56/0.99  --min_unsat_core                        false
% 1.56/0.99  --soft_assumptions                      false
% 1.56/0.99  --soft_lemma_size                       3
% 1.56/0.99  --prop_impl_unit_size                   0
% 1.56/0.99  --prop_impl_unit                        []
% 1.56/0.99  --share_sel_clauses                     true
% 1.56/0.99  --reset_solvers                         false
% 1.56/0.99  --bc_imp_inh                            [conj_cone]
% 1.56/0.99  --conj_cone_tolerance                   3.
% 1.56/0.99  --extra_neg_conj                        none
% 1.56/0.99  --large_theory_mode                     true
% 1.56/0.99  --prolific_symb_bound                   200
% 1.56/0.99  --lt_threshold                          2000
% 1.56/0.99  --clause_weak_htbl                      true
% 1.56/0.99  --gc_record_bc_elim                     false
% 1.56/0.99  
% 1.56/0.99  ------ Preprocessing Options
% 1.56/0.99  
% 1.56/0.99  --preprocessing_flag                    true
% 1.56/0.99  --time_out_prep_mult                    0.1
% 1.56/0.99  --splitting_mode                        input
% 1.56/0.99  --splitting_grd                         true
% 1.56/0.99  --splitting_cvd                         false
% 1.56/0.99  --splitting_cvd_svl                     false
% 1.56/0.99  --splitting_nvd                         32
% 1.56/0.99  --sub_typing                            true
% 1.56/0.99  --prep_gs_sim                           true
% 1.56/0.99  --prep_unflatten                        true
% 1.56/0.99  --prep_res_sim                          true
% 1.56/0.99  --prep_upred                            true
% 1.56/0.99  --prep_sem_filter                       exhaustive
% 1.56/0.99  --prep_sem_filter_out                   false
% 1.56/0.99  --pred_elim                             true
% 1.56/0.99  --res_sim_input                         true
% 1.56/0.99  --eq_ax_congr_red                       true
% 1.56/0.99  --pure_diseq_elim                       true
% 1.56/0.99  --brand_transform                       false
% 1.56/0.99  --non_eq_to_eq                          false
% 1.56/0.99  --prep_def_merge                        true
% 1.56/0.99  --prep_def_merge_prop_impl              false
% 1.56/0.99  --prep_def_merge_mbd                    true
% 1.56/0.99  --prep_def_merge_tr_red                 false
% 1.56/0.99  --prep_def_merge_tr_cl                  false
% 1.56/0.99  --smt_preprocessing                     true
% 1.56/0.99  --smt_ac_axioms                         fast
% 1.56/0.99  --preprocessed_out                      false
% 1.56/0.99  --preprocessed_stats                    false
% 1.56/0.99  
% 1.56/0.99  ------ Abstraction refinement Options
% 1.56/0.99  
% 1.56/0.99  --abstr_ref                             []
% 1.56/0.99  --abstr_ref_prep                        false
% 1.56/0.99  --abstr_ref_until_sat                   false
% 1.56/0.99  --abstr_ref_sig_restrict                funpre
% 1.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/0.99  --abstr_ref_under                       []
% 1.56/0.99  
% 1.56/0.99  ------ SAT Options
% 1.56/0.99  
% 1.56/0.99  --sat_mode                              false
% 1.56/0.99  --sat_fm_restart_options                ""
% 1.56/0.99  --sat_gr_def                            false
% 1.56/0.99  --sat_epr_types                         true
% 1.56/0.99  --sat_non_cyclic_types                  false
% 1.56/0.99  --sat_finite_models                     false
% 1.56/0.99  --sat_fm_lemmas                         false
% 1.56/0.99  --sat_fm_prep                           false
% 1.56/0.99  --sat_fm_uc_incr                        true
% 1.56/0.99  --sat_out_model                         small
% 1.56/0.99  --sat_out_clauses                       false
% 1.56/0.99  
% 1.56/0.99  ------ QBF Options
% 1.56/0.99  
% 1.56/0.99  --qbf_mode                              false
% 1.56/0.99  --qbf_elim_univ                         false
% 1.56/0.99  --qbf_dom_inst                          none
% 1.56/0.99  --qbf_dom_pre_inst                      false
% 1.56/0.99  --qbf_sk_in                             false
% 1.56/0.99  --qbf_pred_elim                         true
% 1.56/0.99  --qbf_split                             512
% 1.56/0.99  
% 1.56/0.99  ------ BMC1 Options
% 1.56/0.99  
% 1.56/0.99  --bmc1_incremental                      false
% 1.56/0.99  --bmc1_axioms                           reachable_all
% 1.56/0.99  --bmc1_min_bound                        0
% 1.56/0.99  --bmc1_max_bound                        -1
% 1.56/0.99  --bmc1_max_bound_default                -1
% 1.56/0.99  --bmc1_symbol_reachability              true
% 1.56/0.99  --bmc1_property_lemmas                  false
% 1.56/0.99  --bmc1_k_induction                      false
% 1.56/0.99  --bmc1_non_equiv_states                 false
% 1.56/0.99  --bmc1_deadlock                         false
% 1.56/0.99  --bmc1_ucm                              false
% 1.56/0.99  --bmc1_add_unsat_core                   none
% 1.56/0.99  --bmc1_unsat_core_children              false
% 1.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/0.99  --bmc1_out_stat                         full
% 1.56/0.99  --bmc1_ground_init                      false
% 1.56/0.99  --bmc1_pre_inst_next_state              false
% 1.56/0.99  --bmc1_pre_inst_state                   false
% 1.56/0.99  --bmc1_pre_inst_reach_state             false
% 1.56/0.99  --bmc1_out_unsat_core                   false
% 1.56/0.99  --bmc1_aig_witness_out                  false
% 1.56/0.99  --bmc1_verbose                          false
% 1.56/0.99  --bmc1_dump_clauses_tptp                false
% 1.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.56/0.99  --bmc1_dump_file                        -
% 1.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.56/0.99  --bmc1_ucm_extend_mode                  1
% 1.56/0.99  --bmc1_ucm_init_mode                    2
% 1.56/0.99  --bmc1_ucm_cone_mode                    none
% 1.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.56/0.99  --bmc1_ucm_relax_model                  4
% 1.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/0.99  --bmc1_ucm_layered_model                none
% 1.56/0.99  --bmc1_ucm_max_lemma_size               10
% 1.56/0.99  
% 1.56/0.99  ------ AIG Options
% 1.56/0.99  
% 1.56/0.99  --aig_mode                              false
% 1.56/0.99  
% 1.56/0.99  ------ Instantiation Options
% 1.56/0.99  
% 1.56/0.99  --instantiation_flag                    true
% 1.56/0.99  --inst_sos_flag                         false
% 1.56/0.99  --inst_sos_phase                        true
% 1.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/0.99  --inst_lit_sel_side                     num_symb
% 1.56/0.99  --inst_solver_per_active                1400
% 1.56/0.99  --inst_solver_calls_frac                1.
% 1.56/0.99  --inst_passive_queue_type               priority_queues
% 1.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/0.99  --inst_passive_queues_freq              [25;2]
% 1.56/0.99  --inst_dismatching                      true
% 1.56/0.99  --inst_eager_unprocessed_to_passive     true
% 1.56/0.99  --inst_prop_sim_given                   true
% 1.56/0.99  --inst_prop_sim_new                     false
% 1.56/0.99  --inst_subs_new                         false
% 1.56/0.99  --inst_eq_res_simp                      false
% 1.56/0.99  --inst_subs_given                       false
% 1.56/0.99  --inst_orphan_elimination               true
% 1.56/0.99  --inst_learning_loop_flag               true
% 1.56/0.99  --inst_learning_start                   3000
% 1.56/0.99  --inst_learning_factor                  2
% 1.56/0.99  --inst_start_prop_sim_after_learn       3
% 1.56/0.99  --inst_sel_renew                        solver
% 1.56/0.99  --inst_lit_activity_flag                true
% 1.56/0.99  --inst_restr_to_given                   false
% 1.56/0.99  --inst_activity_threshold               500
% 1.56/0.99  --inst_out_proof                        true
% 1.56/0.99  
% 1.56/0.99  ------ Resolution Options
% 1.56/0.99  
% 1.56/0.99  --resolution_flag                       true
% 1.56/0.99  --res_lit_sel                           adaptive
% 1.56/0.99  --res_lit_sel_side                      none
% 1.56/0.99  --res_ordering                          kbo
% 1.56/0.99  --res_to_prop_solver                    active
% 1.56/0.99  --res_prop_simpl_new                    false
% 1.56/0.99  --res_prop_simpl_given                  true
% 1.56/0.99  --res_passive_queue_type                priority_queues
% 1.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/0.99  --res_passive_queues_freq               [15;5]
% 1.56/0.99  --res_forward_subs                      full
% 1.56/0.99  --res_backward_subs                     full
% 1.56/0.99  --res_forward_subs_resolution           true
% 1.56/0.99  --res_backward_subs_resolution          true
% 1.56/0.99  --res_orphan_elimination                true
% 1.56/0.99  --res_time_limit                        2.
% 1.56/0.99  --res_out_proof                         true
% 1.56/0.99  
% 1.56/0.99  ------ Superposition Options
% 1.56/0.99  
% 1.56/0.99  --superposition_flag                    true
% 1.56/0.99  --sup_passive_queue_type                priority_queues
% 1.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.56/0.99  --demod_completeness_check              fast
% 1.56/0.99  --demod_use_ground                      true
% 1.56/0.99  --sup_to_prop_solver                    passive
% 1.56/0.99  --sup_prop_simpl_new                    true
% 1.56/0.99  --sup_prop_simpl_given                  true
% 1.56/0.99  --sup_fun_splitting                     false
% 1.56/0.99  --sup_smt_interval                      50000
% 1.56/0.99  
% 1.56/0.99  ------ Superposition Simplification Setup
% 1.56/0.99  
% 1.56/0.99  --sup_indices_passive                   []
% 1.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.99  --sup_full_bw                           [BwDemod]
% 1.56/0.99  --sup_immed_triv                        [TrivRules]
% 1.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.99  --sup_immed_bw_main                     []
% 1.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.99  
% 1.56/0.99  ------ Combination Options
% 1.56/0.99  
% 1.56/0.99  --comb_res_mult                         3
% 1.56/0.99  --comb_sup_mult                         2
% 1.56/0.99  --comb_inst_mult                        10
% 1.56/0.99  
% 1.56/0.99  ------ Debug Options
% 1.56/0.99  
% 1.56/0.99  --dbg_backtrace                         false
% 1.56/0.99  --dbg_dump_prop_clauses                 false
% 1.56/0.99  --dbg_dump_prop_clauses_file            -
% 1.56/0.99  --dbg_out_stat                          false
% 1.56/0.99  ------ Parsing...
% 1.56/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.56/0.99  
% 1.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 1.56/0.99  
% 1.56/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.56/0.99  
% 1.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.56/0.99  ------ Proving...
% 1.56/0.99  ------ Problem Properties 
% 1.56/0.99  
% 1.56/0.99  
% 1.56/0.99  clauses                                 33
% 1.56/0.99  conjectures                             1
% 1.56/0.99  EPR                                     1
% 1.56/0.99  Horn                                    27
% 1.56/0.99  unary                                   1
% 1.56/0.99  binary                                  3
% 1.56/0.99  lits                                    149
% 1.56/0.99  lits eq                                 123
% 1.56/0.99  fd_pure                                 0
% 1.56/0.99  fd_pseudo                               0
% 1.56/0.99  fd_cond                                 0
% 1.56/0.99  fd_pseudo_cond                          0
% 1.56/0.99  AC symbols                              0
% 1.56/0.99  
% 1.56/0.99  ------ Schedule dynamic 5 is on 
% 1.56/0.99  
% 1.56/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.56/0.99  
% 1.56/0.99  
% 1.56/0.99  ------ 
% 1.56/0.99  Current options:
% 1.56/0.99  ------ 
% 1.56/0.99  
% 1.56/0.99  ------ Input Options
% 1.56/0.99  
% 1.56/0.99  --out_options                           all
% 1.56/0.99  --tptp_safe_out                         true
% 1.56/0.99  --problem_path                          ""
% 1.56/0.99  --include_path                          ""
% 1.56/0.99  --clausifier                            res/vclausify_rel
% 1.56/0.99  --clausifier_options                    --mode clausify
% 1.56/0.99  --stdin                                 false
% 1.56/0.99  --stats_out                             all
% 1.56/0.99  
% 1.56/0.99  ------ General Options
% 1.56/0.99  
% 1.56/0.99  --fof                                   false
% 1.56/0.99  --time_out_real                         305.
% 1.56/0.99  --time_out_virtual                      -1.
% 1.56/0.99  --symbol_type_check                     false
% 1.56/0.99  --clausify_out                          false
% 1.56/0.99  --sig_cnt_out                           false
% 1.56/0.99  --trig_cnt_out                          false
% 1.56/0.99  --trig_cnt_out_tolerance                1.
% 1.56/0.99  --trig_cnt_out_sk_spl                   false
% 1.56/0.99  --abstr_cl_out                          false
% 1.56/0.99  
% 1.56/0.99  ------ Global Options
% 1.56/0.99  
% 1.56/0.99  --schedule                              default
% 1.56/0.99  --add_important_lit                     false
% 1.56/0.99  --prop_solver_per_cl                    1000
% 1.56/0.99  --min_unsat_core                        false
% 1.56/0.99  --soft_assumptions                      false
% 1.56/0.99  --soft_lemma_size                       3
% 1.56/0.99  --prop_impl_unit_size                   0
% 1.56/0.99  --prop_impl_unit                        []
% 1.56/0.99  --share_sel_clauses                     true
% 1.56/0.99  --reset_solvers                         false
% 1.56/0.99  --bc_imp_inh                            [conj_cone]
% 1.56/0.99  --conj_cone_tolerance                   3.
% 1.56/0.99  --extra_neg_conj                        none
% 1.56/0.99  --large_theory_mode                     true
% 1.56/0.99  --prolific_symb_bound                   200
% 1.56/0.99  --lt_threshold                          2000
% 1.56/0.99  --clause_weak_htbl                      true
% 1.56/0.99  --gc_record_bc_elim                     false
% 1.56/0.99  
% 1.56/0.99  ------ Preprocessing Options
% 1.56/0.99  
% 1.56/0.99  --preprocessing_flag                    true
% 1.56/0.99  --time_out_prep_mult                    0.1
% 1.56/0.99  --splitting_mode                        input
% 1.56/0.99  --splitting_grd                         true
% 1.56/0.99  --splitting_cvd                         false
% 1.56/0.99  --splitting_cvd_svl                     false
% 1.56/0.99  --splitting_nvd                         32
% 1.56/0.99  --sub_typing                            true
% 1.56/0.99  --prep_gs_sim                           true
% 1.56/0.99  --prep_unflatten                        true
% 1.56/0.99  --prep_res_sim                          true
% 1.56/0.99  --prep_upred                            true
% 1.56/0.99  --prep_sem_filter                       exhaustive
% 1.56/0.99  --prep_sem_filter_out                   false
% 1.56/0.99  --pred_elim                             true
% 1.56/0.99  --res_sim_input                         true
% 1.56/0.99  --eq_ax_congr_red                       true
% 1.56/0.99  --pure_diseq_elim                       true
% 1.56/0.99  --brand_transform                       false
% 1.56/0.99  --non_eq_to_eq                          false
% 1.56/0.99  --prep_def_merge                        true
% 1.56/0.99  --prep_def_merge_prop_impl              false
% 1.56/0.99  --prep_def_merge_mbd                    true
% 1.56/0.99  --prep_def_merge_tr_red                 false
% 1.56/0.99  --prep_def_merge_tr_cl                  false
% 1.56/0.99  --smt_preprocessing                     true
% 1.56/0.99  --smt_ac_axioms                         fast
% 1.56/0.99  --preprocessed_out                      false
% 1.56/0.99  --preprocessed_stats                    false
% 1.56/0.99  
% 1.56/0.99  ------ Abstraction refinement Options
% 1.56/0.99  
% 1.56/0.99  --abstr_ref                             []
% 1.56/0.99  --abstr_ref_prep                        false
% 1.56/0.99  --abstr_ref_until_sat                   false
% 1.56/0.99  --abstr_ref_sig_restrict                funpre
% 1.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/0.99  --abstr_ref_under                       []
% 1.56/0.99  
% 1.56/0.99  ------ SAT Options
% 1.56/0.99  
% 1.56/0.99  --sat_mode                              false
% 1.56/0.99  --sat_fm_restart_options                ""
% 1.56/0.99  --sat_gr_def                            false
% 1.56/0.99  --sat_epr_types                         true
% 1.56/0.99  --sat_non_cyclic_types                  false
% 1.56/0.99  --sat_finite_models                     false
% 1.56/0.99  --sat_fm_lemmas                         false
% 1.56/0.99  --sat_fm_prep                           false
% 1.56/0.99  --sat_fm_uc_incr                        true
% 1.56/0.99  --sat_out_model                         small
% 1.56/0.99  --sat_out_clauses                       false
% 1.56/0.99  
% 1.56/0.99  ------ QBF Options
% 1.56/0.99  
% 1.56/0.99  --qbf_mode                              false
% 1.56/0.99  --qbf_elim_univ                         false
% 1.56/0.99  --qbf_dom_inst                          none
% 1.56/0.99  --qbf_dom_pre_inst                      false
% 1.56/0.99  --qbf_sk_in                             false
% 1.56/0.99  --qbf_pred_elim                         true
% 1.56/0.99  --qbf_split                             512
% 1.56/0.99  
% 1.56/0.99  ------ BMC1 Options
% 1.56/0.99  
% 1.56/0.99  --bmc1_incremental                      false
% 1.56/0.99  --bmc1_axioms                           reachable_all
% 1.56/0.99  --bmc1_min_bound                        0
% 1.56/0.99  --bmc1_max_bound                        -1
% 1.56/0.99  --bmc1_max_bound_default                -1
% 1.56/0.99  --bmc1_symbol_reachability              true
% 1.56/0.99  --bmc1_property_lemmas                  false
% 1.56/0.99  --bmc1_k_induction                      false
% 1.56/0.99  --bmc1_non_equiv_states                 false
% 1.56/0.99  --bmc1_deadlock                         false
% 1.56/0.99  --bmc1_ucm                              false
% 1.56/0.99  --bmc1_add_unsat_core                   none
% 1.56/0.99  --bmc1_unsat_core_children              false
% 1.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/0.99  --bmc1_out_stat                         full
% 1.56/0.99  --bmc1_ground_init                      false
% 1.56/0.99  --bmc1_pre_inst_next_state              false
% 1.56/0.99  --bmc1_pre_inst_state                   false
% 1.56/0.99  --bmc1_pre_inst_reach_state             false
% 1.56/0.99  --bmc1_out_unsat_core                   false
% 1.56/0.99  --bmc1_aig_witness_out                  false
% 1.56/0.99  --bmc1_verbose                          false
% 1.56/0.99  --bmc1_dump_clauses_tptp                false
% 1.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.56/0.99  --bmc1_dump_file                        -
% 1.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.56/0.99  --bmc1_ucm_extend_mode                  1
% 1.56/0.99  --bmc1_ucm_init_mode                    2
% 1.56/0.99  --bmc1_ucm_cone_mode                    none
% 1.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.56/0.99  --bmc1_ucm_relax_model                  4
% 1.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/0.99  --bmc1_ucm_layered_model                none
% 1.56/0.99  --bmc1_ucm_max_lemma_size               10
% 1.56/0.99  
% 1.56/0.99  ------ AIG Options
% 1.56/0.99  
% 1.56/0.99  --aig_mode                              false
% 1.56/0.99  
% 1.56/0.99  ------ Instantiation Options
% 1.56/0.99  
% 1.56/0.99  --instantiation_flag                    true
% 1.56/0.99  --inst_sos_flag                         false
% 1.56/0.99  --inst_sos_phase                        true
% 1.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/0.99  --inst_lit_sel_side                     none
% 1.56/0.99  --inst_solver_per_active                1400
% 1.56/0.99  --inst_solver_calls_frac                1.
% 1.56/0.99  --inst_passive_queue_type               priority_queues
% 1.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/0.99  --inst_passive_queues_freq              [25;2]
% 1.56/0.99  --inst_dismatching                      true
% 1.56/0.99  --inst_eager_unprocessed_to_passive     true
% 1.56/0.99  --inst_prop_sim_given                   true
% 1.56/0.99  --inst_prop_sim_new                     false
% 1.56/0.99  --inst_subs_new                         false
% 1.56/0.99  --inst_eq_res_simp                      false
% 1.56/0.99  --inst_subs_given                       false
% 1.56/0.99  --inst_orphan_elimination               true
% 1.56/0.99  --inst_learning_loop_flag               true
% 1.56/0.99  --inst_learning_start                   3000
% 1.56/0.99  --inst_learning_factor                  2
% 1.56/0.99  --inst_start_prop_sim_after_learn       3
% 1.56/0.99  --inst_sel_renew                        solver
% 1.56/0.99  --inst_lit_activity_flag                true
% 1.56/0.99  --inst_restr_to_given                   false
% 1.56/0.99  --inst_activity_threshold               500
% 1.56/0.99  --inst_out_proof                        true
% 1.56/0.99  
% 1.56/0.99  ------ Resolution Options
% 1.56/0.99  
% 1.56/0.99  --resolution_flag                       false
% 1.56/0.99  --res_lit_sel                           adaptive
% 1.56/0.99  --res_lit_sel_side                      none
% 1.56/0.99  --res_ordering                          kbo
% 1.56/0.99  --res_to_prop_solver                    active
% 1.56/0.99  --res_prop_simpl_new                    false
% 1.56/0.99  --res_prop_simpl_given                  true
% 1.56/0.99  --res_passive_queue_type                priority_queues
% 1.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/0.99  --res_passive_queues_freq               [15;5]
% 1.56/0.99  --res_forward_subs                      full
% 1.56/0.99  --res_backward_subs                     full
% 1.56/0.99  --res_forward_subs_resolution           true
% 1.56/0.99  --res_backward_subs_resolution          true
% 1.56/0.99  --res_orphan_elimination                true
% 1.56/0.99  --res_time_limit                        2.
% 1.56/0.99  --res_out_proof                         true
% 1.56/0.99  
% 1.56/0.99  ------ Superposition Options
% 1.56/0.99  
% 1.56/0.99  --superposition_flag                    true
% 1.56/0.99  --sup_passive_queue_type                priority_queues
% 1.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.56/0.99  --demod_completeness_check              fast
% 1.56/0.99  --demod_use_ground                      true
% 1.56/0.99  --sup_to_prop_solver                    passive
% 1.56/0.99  --sup_prop_simpl_new                    true
% 1.56/0.99  --sup_prop_simpl_given                  true
% 1.56/0.99  --sup_fun_splitting                     false
% 1.56/0.99  --sup_smt_interval                      50000
% 1.56/0.99  
% 1.56/0.99  ------ Superposition Simplification Setup
% 1.56/0.99  
% 1.56/0.99  --sup_indices_passive                   []
% 1.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.99  --sup_full_bw                           [BwDemod]
% 1.56/0.99  --sup_immed_triv                        [TrivRules]
% 1.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.99  --sup_immed_bw_main                     []
% 1.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.99  
% 1.56/0.99  ------ Combination Options
% 1.56/0.99  
% 1.56/0.99  --comb_res_mult                         3
% 1.56/0.99  --comb_sup_mult                         2
% 1.56/0.99  --comb_inst_mult                        10
% 1.56/0.99  
% 1.56/0.99  ------ Debug Options
% 1.56/0.99  
% 1.56/0.99  --dbg_backtrace                         false
% 1.56/0.99  --dbg_dump_prop_clauses                 false
% 1.56/0.99  --dbg_dump_prop_clauses_file            -
% 1.56/0.99  --dbg_out_stat                          false
% 1.56/0.99  
% 1.56/0.99  
% 1.56/0.99  
% 1.56/0.99  
% 1.56/0.99  ------ Proving...
% 1.56/0.99  
% 1.56/0.99  
% 1.56/0.99  % SZS status Theorem for theBenchmark.p
% 1.56/0.99  
% 1.56/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.56/0.99  
% 1.56/0.99  fof(f7,conjecture,(
% 1.56/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.56/0.99  
% 1.56/0.99  fof(f8,negated_conjecture,(
% 1.56/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.56/0.99    inference(negated_conjecture,[],[f7])).
% 1.56/0.99  
% 1.56/0.99  fof(f16,plain,(
% 1.56/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.56/0.99    inference(ennf_transformation,[],[f8])).
% 1.56/0.99  
% 1.56/0.99  fof(f17,plain,(
% 1.56/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.56/0.99    inference(flattening,[],[f16])).
% 1.56/0.99  
% 1.56/0.99  fof(f19,plain,(
% 1.56/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.56/0.99    introduced(choice_axiom,[])).
% 1.56/0.99  
% 1.56/0.99  fof(f20,plain,(
% 1.56/0.99    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).
% 1.56/0.99  
% 1.56/0.99  fof(f35,plain,(
% 1.56/0.99    v1_funct_2(sK3,sK0,sK1)),
% 1.56/0.99    inference(cnf_transformation,[],[f20])).
% 1.56/0.99  
% 1.56/0.99  fof(f5,axiom,(
% 1.56/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.56/0.99  
% 1.56/0.99  fof(f12,plain,(
% 1.56/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(ennf_transformation,[],[f5])).
% 1.56/1.00  
% 1.56/1.00  fof(f13,plain,(
% 1.56/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(flattening,[],[f12])).
% 1.56/1.00  
% 1.56/1.00  fof(f18,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(nnf_transformation,[],[f13])).
% 1.56/1.00  
% 1.56/1.00  fof(f25,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f18])).
% 1.56/1.00  
% 1.56/1.00  fof(f36,plain,(
% 1.56/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/1.00    inference(cnf_transformation,[],[f20])).
% 1.56/1.00  
% 1.56/1.00  fof(f3,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f10,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(ennf_transformation,[],[f3])).
% 1.56/1.00  
% 1.56/1.00  fof(f23,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f10])).
% 1.56/1.00  
% 1.56/1.00  fof(f30,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f18])).
% 1.56/1.00  
% 1.56/1.00  fof(f40,plain,(
% 1.56/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(equality_resolution,[],[f30])).
% 1.56/1.00  
% 1.56/1.00  fof(f41,plain,(
% 1.56/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.56/1.00    inference(equality_resolution,[],[f40])).
% 1.56/1.00  
% 1.56/1.00  fof(f39,plain,(
% 1.56/1.00    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 1.56/1.00    inference(cnf_transformation,[],[f20])).
% 1.56/1.00  
% 1.56/1.00  fof(f34,plain,(
% 1.56/1.00    v1_funct_1(sK3)),
% 1.56/1.00    inference(cnf_transformation,[],[f20])).
% 1.56/1.00  
% 1.56/1.00  fof(f6,axiom,(
% 1.56/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f14,plain,(
% 1.56/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.56/1.00    inference(ennf_transformation,[],[f6])).
% 1.56/1.00  
% 1.56/1.00  fof(f15,plain,(
% 1.56/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.56/1.00    inference(flattening,[],[f14])).
% 1.56/1.00  
% 1.56/1.00  fof(f33,plain,(
% 1.56/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f15])).
% 1.56/1.00  
% 1.56/1.00  fof(f37,plain,(
% 1.56/1.00    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.56/1.00    inference(cnf_transformation,[],[f20])).
% 1.56/1.00  
% 1.56/1.00  fof(f32,plain,(
% 1.56/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f15])).
% 1.56/1.00  
% 1.56/1.00  fof(f4,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f11,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(ennf_transformation,[],[f4])).
% 1.56/1.00  
% 1.56/1.00  fof(f24,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f11])).
% 1.56/1.00  
% 1.56/1.00  fof(f1,axiom,(
% 1.56/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f9,plain,(
% 1.56/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(ennf_transformation,[],[f1])).
% 1.56/1.00  
% 1.56/1.00  fof(f21,plain,(
% 1.56/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f9])).
% 1.56/1.00  
% 1.56/1.00  fof(f2,axiom,(
% 1.56/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f22,plain,(
% 1.56/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f2])).
% 1.56/1.00  
% 1.56/1.00  fof(f29,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f18])).
% 1.56/1.00  
% 1.56/1.00  fof(f42,plain,(
% 1.56/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.56/1.00    inference(equality_resolution,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f38,plain,(
% 1.56/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.56/1.00    inference(cnf_transformation,[],[f20])).
% 1.56/1.00  
% 1.56/1.00  fof(f26,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f18])).
% 1.56/1.00  
% 1.56/1.00  fof(f44,plain,(
% 1.56/1.00    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.56/1.00    inference(equality_resolution,[],[f26])).
% 1.56/1.00  
% 1.56/1.00  fof(f28,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f18])).
% 1.56/1.00  
% 1.56/1.00  fof(f43,plain,(
% 1.56/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_relset_1(k1_xboole_0,X1,X2) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.56/1.00    inference(equality_resolution,[],[f28])).
% 1.56/1.00  
% 1.56/1.00  cnf(c_17,negated_conjecture,
% 1.56/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 1.56/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_9,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 1.56/1.00      | k1_xboole_0 = X2 ),
% 1.56/1.00      inference(cnf_transformation,[],[f25]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_16,negated_conjecture,
% 1.56/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.56/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_296,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK3 != X0
% 1.56/1.00      | k1_xboole_0 = X2 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_297,plain,
% 1.56/1.00      ( ~ v1_funct_2(sK3,X0,X1)
% 1.56/1.00      | k1_relset_1(X0,X1,sK3) = X0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k1_xboole_0 = X1 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_296]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1060,plain,
% 1.56/1.00      ( k1_relset_1(X0,X1,sK3) = X0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK1 != X1
% 1.56/1.00      | sK0 != X0
% 1.56/1.00      | sK3 != sK3
% 1.56/1.00      | k1_xboole_0 = X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_297]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1061,plain,
% 1.56/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k1_xboole_0 = sK1 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_1060]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1409,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 1.56/1.00      | k1_xboole_0 = sK1 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_1061]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1854,plain,
% 1.56/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 1.56/1.00      inference(equality_resolution_simp,[status(thm)],[c_1409]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2,plain,
% 1.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.56/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f23]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_341,plain,
% 1.56/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK3 != X2 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_16]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_342,plain,
% 1.56/1.00      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_341]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1427,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k1_relset_1(X0_44,X1_44,sK3) = k1_relat_1(sK3) ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_342]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2146,plain,
% 1.56/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 1.56/1.00      inference(equality_resolution,[status(thm)],[c_1427]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2227,plain,
% 1.56/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 1.56/1.00      inference(demodulation,[status(thm)],[c_1854,c_2146]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_4,plain,
% 1.56/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 1.56/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 1.56/1.00      | k1_xboole_0 = X0 ),
% 1.56/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_434,plain,
% 1.56/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK3 != k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_13,negated_conjecture,
% 1.56/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 1.56/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 1.56/1.00      | ~ v1_funct_1(sK3) ),
% 1.56/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_18,negated_conjecture,
% 1.56/1.00      ( v1_funct_1(sK3) ),
% 1.56/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_100,plain,
% 1.56/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 1.56/1.00      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_13,c_18]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_101,negated_conjecture,
% 1.56/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 1.56/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_100]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_10,plain,
% 1.56/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.56/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.56/1.00      | ~ v1_funct_1(X0)
% 1.56/1.00      | ~ v1_relat_1(X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_15,negated_conjecture,
% 1.56/1.00      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 1.56/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_217,plain,
% 1.56/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.56/1.00      | ~ v1_funct_1(X0)
% 1.56/1.00      | ~ v1_relat_1(X0)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
% 1.56/1.00      | sK2 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_218,plain,
% 1.56/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
% 1.56/1.00      | ~ v1_funct_1(X0)
% 1.56/1.00      | ~ v1_relat_1(X0)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_217]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_245,plain,
% 1.56/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
% 1.56/1.00      | ~ v1_relat_1(X0)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
% 1.56/1.00      | sK3 != X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_218,c_18]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_246,plain,
% 1.56/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_600,plain,
% 1.56/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | sK3 != sK3 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_101,c_246]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_772,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | sK2 != k1_xboole_0
% 1.56/1.00      | sK0 != X0
% 1.56/1.00      | sK3 != sK3
% 1.56/1.00      | sK3 != k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_434,c_600]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_773,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK2 != k1_xboole_0
% 1.56/1.00      | sK3 != k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_772]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1422,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | sK2 != k1_xboole_0
% 1.56/1.00      | sK3 != k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_773]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1807,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | sK2 != k1_xboole_0
% 1.56/1.00      | sK3 != k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = sK0
% 1.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1422]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_11,plain,
% 1.56/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.56/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.56/1.00      | ~ v1_funct_1(X0)
% 1.56/1.00      | ~ v1_relat_1(X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_199,plain,
% 1.56/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.56/1.00      | ~ v1_funct_1(X0)
% 1.56/1.00      | ~ v1_relat_1(X0)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
% 1.56/1.00      | sK2 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_200,plain,
% 1.56/1.00      ( v1_funct_2(X0,k1_relat_1(X0),sK2)
% 1.56/1.00      | ~ v1_funct_1(X0)
% 1.56/1.00      | ~ v1_relat_1(X0)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_199]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_258,plain,
% 1.56/1.00      ( v1_funct_2(X0,k1_relat_1(X0),sK2)
% 1.56/1.00      | ~ v1_relat_1(X0)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
% 1.56/1.00      | sK3 != X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_200,c_18]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_259,plain,
% 1.56/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),sK2)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_258]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_872,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relat_1(sK3) != sK0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | sK2 != sK2
% 1.56/1.00      | sK3 != sK3 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_600,c_259]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1418,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relat_1(sK3) != sK0
% 1.56/1.00      | sK2 != sK2
% 1.56/1.00      | sK3 != sK3 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_872]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1529,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relat_1(sK3) != sK0 ),
% 1.56/1.00      inference(equality_resolution_simp,[status(thm)],[c_1418]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_3,plain,
% 1.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.56/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f24]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_332,plain,
% 1.56/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK3 != X2 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_333,plain,
% 1.56/1.00      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_332]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1428,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k2_relset_1(X0_44,X1_44,sK3) = k2_relat_1(sK3) ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_333]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2149,plain,
% 1.56/1.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 1.56/1.00      inference(equality_resolution,[status(thm)],[c_1428]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_0,plain,
% 1.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.56/1.00      | ~ v1_relat_1(X1)
% 1.56/1.00      | v1_relat_1(X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f21]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_279,plain,
% 1.56/1.00      ( ~ v1_relat_1(X0)
% 1.56/1.00      | v1_relat_1(X1)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 1.56/1.00      | sK3 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_280,plain,
% 1.56/1.00      ( ~ v1_relat_1(X0)
% 1.56/1.00      | v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_279]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1429,plain,
% 1.56/1.00      ( ~ v1_relat_1(X0_44)
% 1.56/1.00      | v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_44) ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_280]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1800,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_44)
% 1.56/1.00      | v1_relat_1(X0_44) != iProver_top
% 1.56/1.00      | v1_relat_1(sK3) = iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2234,plain,
% 1.56/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 1.56/1.00      | v1_relat_1(sK3) = iProver_top ),
% 1.56/1.00      inference(equality_resolution,[status(thm)],[c_1800]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2235,plain,
% 1.56/1.00      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) ),
% 1.56/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2234]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1,plain,
% 1.56/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.56/1.00      inference(cnf_transformation,[],[f22]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1431,plain,
% 1.56/1.00      ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2239,plain,
% 1.56/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1431]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_5,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 1.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 1.56/1.00      | k1_xboole_0 = X1
% 1.56/1.00      | k1_xboole_0 = X0 ),
% 1.56/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_492,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
% 1.56/1.00      | sK3 != X0
% 1.56/1.00      | k1_xboole_0 = X1
% 1.56/1.00      | k1_xboole_0 = X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_246]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_493,plain,
% 1.56/1.00      ( ~ v1_funct_2(sK3,X0,k1_xboole_0)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 1.56/1.00      | k1_xboole_0 = X0
% 1.56/1.00      | k1_xboole_0 = sK3 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_492]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1071,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 1.56/1.00      | sK1 != k1_xboole_0
% 1.56/1.00      | sK0 != X0
% 1.56/1.00      | sK3 != sK3
% 1.56/1.00      | sK3 = k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_493]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1072,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
% 1.56/1.00      | sK1 != k1_xboole_0
% 1.56/1.00      | sK3 = k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_1071]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1408,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | sK1 != k1_xboole_0
% 1.56/1.00      | sK3 = k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_1072]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1816,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | sK1 != k1_xboole_0
% 1.56/1.00      | sK3 = k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = sK0
% 1.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1408]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1437,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1458,plain,
% 1.56/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1437]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_14,negated_conjecture,
% 1.56/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1430,negated_conjecture,
% 1.56/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1440,plain,
% 1.56/1.00      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 1.56/1.00      theory(equality) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2265,plain,
% 1.56/1.00      ( X0_44 != X1_44 | X0_44 = sK1 | sK1 != X1_44 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1440]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2266,plain,
% 1.56/1.00      ( sK1 != k1_xboole_0
% 1.56/1.00      | k1_xboole_0 = sK1
% 1.56/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_2265]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2372,plain,
% 1.56/1.00      ( k1_xboole_0 = sK0 | sK1 != k1_xboole_0 ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_1816,c_1458,c_1430,c_2266]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2373,plain,
% 1.56/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_2372]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2578,plain,
% 1.56/1.00      ( k1_xboole_0 = sK0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_1807,c_1529,c_2149,c_2227,c_2235,c_2239,c_2373]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2579,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_xboole_0 = sK0 ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_2578]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2582,plain,
% 1.56/1.00      ( sK1 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 1.56/1.00      inference(superposition,[status(thm)],[c_2227,c_2579]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2173,plain,
% 1.56/1.00      ( sK0 != X0_44 | sK0 = k1_xboole_0 | k1_xboole_0 != X0_44 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1440]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2185,plain,
% 1.56/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_2173]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2186,plain,
% 1.56/1.00      ( sK0 = sK0 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1437]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2879,plain,
% 1.56/1.00      ( sK0 = k1_xboole_0 ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_2582,c_2185,c_2186,c_2373]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2901,plain,
% 1.56/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
% 1.56/1.00      inference(demodulation,[status(thm)],[c_2879,c_2146]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_8,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.56/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_516,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK3 != X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_517,plain,
% 1.56/1.00      ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1126,plain,
% 1.56/1.00      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK1 != X0
% 1.56/1.00      | sK0 != k1_xboole_0
% 1.56/1.00      | sK3 != sK3 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_517]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1127,plain,
% 1.56/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | sK0 != k1_xboole_0 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_1126]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1405,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 1.56/1.00      | sK0 != k1_xboole_0 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_1127]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2903,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 1.56/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.56/1.00      inference(demodulation,[status(thm)],[c_2879,c_1405]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2915,plain,
% 1.56/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0 ),
% 1.56/1.00      inference(equality_resolution_simp,[status(thm)],[c_2903]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2918,plain,
% 1.56/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.56/1.00      inference(light_normalisation,[status(thm)],[c_2901,c_2915]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_546,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))
% 1.56/1.00      | sK3 != X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_246]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_547,plain,
% 1.56/1.00      ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_546]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1187,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.56/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.56/1.00      | sK2 != X0
% 1.56/1.00      | sK3 != sK3 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_259,c_547]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1188,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.56/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_1187]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1402,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.56/1.00      | k1_relat_1(sK3) != k1_xboole_0 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_1188]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1820,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.56/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 1.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2665,plain,
% 1.56/1.00      ( k1_relat_1(sK3) != k1_xboole_0
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_1820,c_1402,c_2149,c_2235,c_2239]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2666,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.56/1.00      | k1_relat_1(sK3) != k1_xboole_0 ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_2665]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_3107,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.56/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.56/1.00      inference(demodulation,[status(thm)],[c_2918,c_2666]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_3118,plain,
% 1.56/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0 ),
% 1.56/1.00      inference(equality_resolution_simp,[status(thm)],[c_3107]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_6,plain,
% 1.56/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.56/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_567,plain,
% 1.56/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))
% 1.56/1.00      | sK3 != X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_246]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_568,plain,
% 1.56/1.00      ( v1_funct_2(sK3,k1_xboole_0,X0)
% 1.56/1.00      | ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X0,sK3) != k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_567]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_961,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,X0,sK3) != k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.56/1.00      | sK2 != X0
% 1.56/1.00      | sK0 != k1_xboole_0
% 1.56/1.00      | sK3 != sK3 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_600,c_568]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_962,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | sK0 != k1_xboole_0 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_961]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1414,plain,
% 1.56/1.00      ( ~ v1_relat_1(sK3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 1.56/1.00      | sK0 != k1_xboole_0 ),
% 1.56/1.00      inference(subtyping,[status(esa)],[c_962]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1812,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 1.56/1.00      | sK0 != k1_xboole_0
% 1.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1414]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2758,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_1812,c_1414,c_2149,c_2185,c_2186,c_2235,c_2239,c_2373,
% 1.56/1.00                 c_2582]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2759,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_2758]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2884,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
% 1.56/1.00      inference(demodulation,[status(thm)],[c_2879,c_2759]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2952,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))
% 1.56/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
% 1.56/1.00      inference(light_normalisation,[status(thm)],[c_2884,c_2918]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2953,plain,
% 1.56/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
% 1.56/1.00      inference(equality_resolution_simp,[status(thm)],[c_2952]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(contradiction,plain,
% 1.56/1.00      ( $false ),
% 1.56/1.00      inference(minisat,[status(thm)],[c_3118,c_2953]) ).
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  ------                               Statistics
% 1.56/1.00  
% 1.56/1.00  ------ General
% 1.56/1.00  
% 1.56/1.00  abstr_ref_over_cycles:                  0
% 1.56/1.00  abstr_ref_under_cycles:                 0
% 1.56/1.00  gc_basic_clause_elim:                   0
% 1.56/1.00  forced_gc_time:                         0
% 1.56/1.00  parsing_time:                           0.007
% 1.56/1.00  unif_index_cands_time:                  0.
% 1.56/1.00  unif_index_add_time:                    0.
% 1.56/1.00  orderings_time:                         0.
% 1.56/1.00  out_proof_time:                         0.012
% 1.56/1.00  total_time:                             0.123
% 1.56/1.00  num_of_symbols:                         52
% 1.56/1.00  num_of_terms:                           1591
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing
% 1.56/1.00  
% 1.56/1.00  num_of_splits:                          2
% 1.56/1.00  num_of_split_atoms:                     2
% 1.56/1.00  num_of_reused_defs:                     0
% 1.56/1.00  num_eq_ax_congr_red:                    4
% 1.56/1.00  num_of_sem_filtered_clauses:            1
% 1.56/1.00  num_of_subtypes:                        3
% 1.56/1.00  monotx_restored_types:                  0
% 1.56/1.00  sat_num_of_epr_types:                   0
% 1.56/1.00  sat_num_of_non_cyclic_types:            0
% 1.56/1.00  sat_guarded_non_collapsed_types:        0
% 1.56/1.00  num_pure_diseq_elim:                    0
% 1.56/1.00  simp_replaced_by:                       0
% 1.56/1.00  res_preprocessed:                       109
% 1.56/1.00  prep_upred:                             0
% 1.56/1.00  prep_unflattend:                        104
% 1.56/1.00  smt_new_axioms:                         0
% 1.56/1.00  pred_elim_cands:                        5
% 1.56/1.00  pred_elim:                              4
% 1.56/1.00  pred_elim_cl:                           -13
% 1.56/1.00  pred_elim_cycles:                       5
% 1.56/1.00  merged_defs:                            0
% 1.56/1.00  merged_defs_ncl:                        0
% 1.56/1.00  bin_hyper_res:                          0
% 1.56/1.00  prep_cycles:                            3
% 1.56/1.00  pred_elim_time:                         0.027
% 1.56/1.00  splitting_time:                         0.
% 1.56/1.00  sem_filter_time:                        0.
% 1.56/1.00  monotx_time:                            0.
% 1.56/1.00  subtype_inf_time:                       0.
% 1.56/1.00  
% 1.56/1.00  ------ Problem properties
% 1.56/1.00  
% 1.56/1.00  clauses:                                33
% 1.56/1.00  conjectures:                            1
% 1.56/1.00  epr:                                    1
% 1.56/1.00  horn:                                   27
% 1.56/1.00  ground:                                 27
% 1.56/1.00  unary:                                  1
% 1.56/1.00  binary:                                 3
% 1.56/1.00  lits:                                   149
% 1.56/1.00  lits_eq:                                123
% 1.56/1.00  fd_pure:                                0
% 1.56/1.00  fd_pseudo:                              0
% 1.56/1.00  fd_cond:                                0
% 1.56/1.00  fd_pseudo_cond:                         0
% 1.56/1.00  ac_symbols:                             0
% 1.56/1.00  
% 1.56/1.00  ------ Propositional Solver
% 1.56/1.00  
% 1.56/1.00  prop_solver_calls:                      24
% 1.56/1.00  prop_fast_solver_calls:                 1226
% 1.56/1.00  smt_solver_calls:                       0
% 1.56/1.00  smt_fast_solver_calls:                  0
% 1.56/1.00  prop_num_of_clauses:                    627
% 1.56/1.00  prop_preprocess_simplified:             2607
% 1.56/1.00  prop_fo_subsumed:                       60
% 1.56/1.00  prop_solver_time:                       0.
% 1.56/1.00  smt_solver_time:                        0.
% 1.56/1.00  smt_fast_solver_time:                   0.
% 1.56/1.00  prop_fast_solver_time:                  0.
% 1.56/1.00  prop_unsat_core_time:                   0.
% 1.56/1.00  
% 1.56/1.00  ------ QBF
% 1.56/1.00  
% 1.56/1.00  qbf_q_res:                              0
% 1.56/1.00  qbf_num_tautologies:                    0
% 1.56/1.00  qbf_prep_cycles:                        0
% 1.56/1.00  
% 1.56/1.00  ------ BMC1
% 1.56/1.00  
% 1.56/1.00  bmc1_current_bound:                     -1
% 1.56/1.00  bmc1_last_solved_bound:                 -1
% 1.56/1.00  bmc1_unsat_core_size:                   -1
% 1.56/1.00  bmc1_unsat_core_parents_size:           -1
% 1.56/1.00  bmc1_merge_next_fun:                    0
% 1.56/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.56/1.00  
% 1.56/1.00  ------ Instantiation
% 1.56/1.00  
% 1.56/1.00  inst_num_of_clauses:                    225
% 1.56/1.00  inst_num_in_passive:                    28
% 1.56/1.00  inst_num_in_active:                     167
% 1.56/1.00  inst_num_in_unprocessed:                30
% 1.56/1.00  inst_num_of_loops:                      200
% 1.56/1.00  inst_num_of_learning_restarts:          0
% 1.56/1.00  inst_num_moves_active_passive:          28
% 1.56/1.00  inst_lit_activity:                      0
% 1.56/1.00  inst_lit_activity_moves:                0
% 1.56/1.00  inst_num_tautologies:                   0
% 1.56/1.00  inst_num_prop_implied:                  0
% 1.56/1.00  inst_num_existing_simplified:           0
% 1.56/1.00  inst_num_eq_res_simplified:             0
% 1.56/1.00  inst_num_child_elim:                    0
% 1.56/1.00  inst_num_of_dismatching_blockings:      81
% 1.56/1.00  inst_num_of_non_proper_insts:           248
% 1.56/1.00  inst_num_of_duplicates:                 0
% 1.56/1.00  inst_inst_num_from_inst_to_res:         0
% 1.56/1.00  inst_dismatching_checking_time:         0.
% 1.56/1.00  
% 1.56/1.00  ------ Resolution
% 1.56/1.00  
% 1.56/1.00  res_num_of_clauses:                     0
% 1.56/1.00  res_num_in_passive:                     0
% 1.56/1.00  res_num_in_active:                      0
% 1.56/1.00  res_num_of_loops:                       112
% 1.56/1.00  res_forward_subset_subsumed:            55
% 1.56/1.00  res_backward_subset_subsumed:           0
% 1.56/1.00  res_forward_subsumed:                   4
% 1.56/1.00  res_backward_subsumed:                  0
% 1.56/1.00  res_forward_subsumption_resolution:     0
% 1.56/1.00  res_backward_subsumption_resolution:    0
% 1.56/1.00  res_clause_to_clause_subsumption:       111
% 1.56/1.00  res_orphan_elimination:                 0
% 1.56/1.00  res_tautology_del:                      93
% 1.56/1.00  res_num_eq_res_simplified:              5
% 1.56/1.00  res_num_sel_changes:                    0
% 1.56/1.00  res_moves_from_active_to_pass:          0
% 1.56/1.00  
% 1.56/1.00  ------ Superposition
% 1.56/1.00  
% 1.56/1.00  sup_time_total:                         0.
% 1.56/1.00  sup_time_generating:                    0.
% 1.56/1.00  sup_time_sim_full:                      0.
% 1.56/1.00  sup_time_sim_immed:                     0.
% 1.56/1.00  
% 1.56/1.00  sup_num_of_clauses:                     26
% 1.56/1.00  sup_num_in_active:                      9
% 1.56/1.00  sup_num_in_passive:                     17
% 1.56/1.00  sup_num_of_loops:                       38
% 1.56/1.00  sup_fw_superposition:                   12
% 1.56/1.00  sup_bw_superposition:                   0
% 1.56/1.00  sup_immediate_simplified:               17
% 1.56/1.00  sup_given_eliminated:                   0
% 1.56/1.00  comparisons_done:                       0
% 1.56/1.00  comparisons_avoided:                    3
% 1.56/1.00  
% 1.56/1.00  ------ Simplifications
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  sim_fw_subset_subsumed:                 9
% 1.56/1.00  sim_bw_subset_subsumed:                 3
% 1.56/1.00  sim_fw_subsumed:                        0
% 1.56/1.00  sim_bw_subsumed:                        1
% 1.56/1.00  sim_fw_subsumption_res:                 0
% 1.56/1.00  sim_bw_subsumption_res:                 0
% 1.56/1.00  sim_tautology_del:                      0
% 1.56/1.00  sim_eq_tautology_del:                   6
% 1.56/1.00  sim_eq_res_simp:                        13
% 1.56/1.00  sim_fw_demodulated:                     1
% 1.56/1.00  sim_bw_demodulated:                     30
% 1.56/1.00  sim_light_normalised:                   5
% 1.56/1.00  sim_joinable_taut:                      0
% 1.56/1.00  sim_joinable_simp:                      0
% 1.56/1.00  sim_ac_normalised:                      0
% 1.56/1.00  sim_smt_subsumption:                    0
% 1.56/1.00  
%------------------------------------------------------------------------------
