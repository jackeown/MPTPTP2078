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
% DateTime   : Thu Dec  3 12:00:32 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  170 (3317 expanded)
%              Number of clauses        :  120 (1182 expanded)
%              Number of leaves         :   16 ( 626 expanded)
%              Depth                    :   25
%              Number of atoms          :  526 (18699 expanded)
%              Number of equality atoms :  325 (6034 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f24,plain,
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

fof(f25,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).

fof(f42,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f49])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_309,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_311,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_18])).

cnf(c_697,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_699,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1423,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_697,c_699])).

cnf(c_1501,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_311,c_1423])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_698,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1215,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_697,c_698])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_696,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_197])).

cnf(c_1261,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1215,c_696])).

cnf(c_1269,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1261])).

cnf(c_1537,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_1269])).

cnf(c_1556,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1537,c_699])).

cnf(c_12,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_97,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_20])).

cnf(c_98,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_97])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_98])).

cnf(c_296,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_691,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_1639,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1556,c_691])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_841,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_849,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_940,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_941,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_1691,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1639,c_18,c_23,c_841,c_941])).

cnf(c_1692,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1691])).

cnf(c_1695,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1501,c_1692])).

cnf(c_1824,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1695,c_697])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1832,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1824,c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_53,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_458,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_862,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_460,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1124,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK2))
    | k2_zfmisc_1(sK0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1572,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK2))
    | k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1575,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK2))
    | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_461,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_1573,plain,
    ( k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(X0,X1)
    | sK2 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_1578,plain,
    ( k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1013,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1170,plain,
    ( m1_subset_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_1593,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_1595,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1593])).

cnf(c_1597,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_462,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1594,plain,
    ( X0 != k2_zfmisc_1(sK0,sK2)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_1599,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_1672,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1674,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1825,plain,
    ( sK2 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1695,c_16])).

cnf(c_1915,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1537])).

cnf(c_1926,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1915,c_2])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2018,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2132,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1832,c_18,c_23,c_53,c_0,c_841,c_862,c_941,c_1575,c_1578,c_1597,c_1599,c_1674,c_1926,c_2018])).

cnf(c_1538,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1269])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_700,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1724,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_700])).

cnf(c_57,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_892,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_893,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_895,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_1810,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_57,c_895])).

cnf(c_2138,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2132,c_1810])).

cnf(c_701,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2369,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2138,c_701])).

cnf(c_2716,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2369,c_2132])).

cnf(c_1425,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_699])).

cnf(c_2141,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2132,c_1425])).

cnf(c_11,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_98])).

cnf(c_267,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_693,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_775,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_693,c_3])).

cnf(c_2282,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2141,c_775])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_283,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_692,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_753,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_692,c_3])).

cnf(c_2283,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2141,c_753])).

cnf(c_2294,plain,
    ( sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2282,c_2283])).

cnf(c_9,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_223,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK0 != X0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_98])).

cnf(c_224,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_695,plain,
    ( sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_784,plain,
    ( sK2 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_695,c_2])).

cnf(c_1138,plain,
    ( sK3 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_18,c_23,c_841,c_941])).

cnf(c_1139,plain,
    ( sK2 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1138])).

cnf(c_1916,plain,
    ( sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1139])).

cnf(c_856,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_859,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_459,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_944,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_1178,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_1179,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_1555,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_700])).

cnf(c_1912,plain,
    ( sK0 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1555])).

cnf(c_1940,plain,
    ( sK0 = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1912,c_2])).

cnf(c_1953,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1916,c_57,c_859,c_862,c_1139,c_1179,c_1825,c_1940])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2716,c_2294,c_2132,c_1953,c_941,c_841,c_23,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:13:31 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.37/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/0.96  
% 2.37/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.37/0.96  
% 2.37/0.96  ------  iProver source info
% 2.37/0.96  
% 2.37/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.37/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.37/0.96  git: non_committed_changes: false
% 2.37/0.96  git: last_make_outside_of_git: false
% 2.37/0.96  
% 2.37/0.96  ------ 
% 2.37/0.96  
% 2.37/0.96  ------ Input Options
% 2.37/0.96  
% 2.37/0.96  --out_options                           all
% 2.37/0.96  --tptp_safe_out                         true
% 2.37/0.96  --problem_path                          ""
% 2.37/0.96  --include_path                          ""
% 2.37/0.96  --clausifier                            res/vclausify_rel
% 2.37/0.96  --clausifier_options                    --mode clausify
% 2.37/0.96  --stdin                                 false
% 2.37/0.96  --stats_out                             all
% 2.37/0.96  
% 2.37/0.96  ------ General Options
% 2.37/0.96  
% 2.37/0.96  --fof                                   false
% 2.37/0.96  --time_out_real                         305.
% 2.37/0.96  --time_out_virtual                      -1.
% 2.37/0.96  --symbol_type_check                     false
% 2.37/0.96  --clausify_out                          false
% 2.37/0.96  --sig_cnt_out                           false
% 2.37/0.96  --trig_cnt_out                          false
% 2.37/0.96  --trig_cnt_out_tolerance                1.
% 2.37/0.96  --trig_cnt_out_sk_spl                   false
% 2.37/0.96  --abstr_cl_out                          false
% 2.37/0.96  
% 2.37/0.96  ------ Global Options
% 2.37/0.96  
% 2.37/0.96  --schedule                              default
% 2.37/0.96  --add_important_lit                     false
% 2.37/0.96  --prop_solver_per_cl                    1000
% 2.37/0.96  --min_unsat_core                        false
% 2.37/0.96  --soft_assumptions                      false
% 2.37/0.96  --soft_lemma_size                       3
% 2.37/0.96  --prop_impl_unit_size                   0
% 2.37/0.96  --prop_impl_unit                        []
% 2.37/0.96  --share_sel_clauses                     true
% 2.37/0.96  --reset_solvers                         false
% 2.37/0.96  --bc_imp_inh                            [conj_cone]
% 2.37/0.96  --conj_cone_tolerance                   3.
% 2.37/0.96  --extra_neg_conj                        none
% 2.37/0.96  --large_theory_mode                     true
% 2.37/0.96  --prolific_symb_bound                   200
% 2.37/0.96  --lt_threshold                          2000
% 2.37/0.96  --clause_weak_htbl                      true
% 2.37/0.96  --gc_record_bc_elim                     false
% 2.37/0.96  
% 2.37/0.96  ------ Preprocessing Options
% 2.37/0.96  
% 2.37/0.96  --preprocessing_flag                    true
% 2.37/0.96  --time_out_prep_mult                    0.1
% 2.37/0.96  --splitting_mode                        input
% 2.37/0.96  --splitting_grd                         true
% 2.37/0.96  --splitting_cvd                         false
% 2.37/0.96  --splitting_cvd_svl                     false
% 2.37/0.96  --splitting_nvd                         32
% 2.37/0.96  --sub_typing                            true
% 2.37/0.96  --prep_gs_sim                           true
% 2.37/0.96  --prep_unflatten                        true
% 2.37/0.96  --prep_res_sim                          true
% 2.37/0.96  --prep_upred                            true
% 2.37/0.96  --prep_sem_filter                       exhaustive
% 2.37/0.96  --prep_sem_filter_out                   false
% 2.37/0.96  --pred_elim                             true
% 2.37/0.96  --res_sim_input                         true
% 2.37/0.96  --eq_ax_congr_red                       true
% 2.37/0.96  --pure_diseq_elim                       true
% 2.37/0.96  --brand_transform                       false
% 2.37/0.96  --non_eq_to_eq                          false
% 2.37/0.96  --prep_def_merge                        true
% 2.37/0.96  --prep_def_merge_prop_impl              false
% 2.37/0.96  --prep_def_merge_mbd                    true
% 2.37/0.96  --prep_def_merge_tr_red                 false
% 2.37/0.96  --prep_def_merge_tr_cl                  false
% 2.37/0.96  --smt_preprocessing                     true
% 2.37/0.96  --smt_ac_axioms                         fast
% 2.37/0.96  --preprocessed_out                      false
% 2.37/0.96  --preprocessed_stats                    false
% 2.37/0.96  
% 2.37/0.96  ------ Abstraction refinement Options
% 2.37/0.96  
% 2.37/0.96  --abstr_ref                             []
% 2.37/0.96  --abstr_ref_prep                        false
% 2.37/0.96  --abstr_ref_until_sat                   false
% 2.37/0.96  --abstr_ref_sig_restrict                funpre
% 2.37/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/0.96  --abstr_ref_under                       []
% 2.37/0.96  
% 2.37/0.96  ------ SAT Options
% 2.37/0.96  
% 2.37/0.96  --sat_mode                              false
% 2.37/0.96  --sat_fm_restart_options                ""
% 2.37/0.96  --sat_gr_def                            false
% 2.37/0.96  --sat_epr_types                         true
% 2.37/0.96  --sat_non_cyclic_types                  false
% 2.37/0.96  --sat_finite_models                     false
% 2.37/0.96  --sat_fm_lemmas                         false
% 2.37/0.96  --sat_fm_prep                           false
% 2.37/0.96  --sat_fm_uc_incr                        true
% 2.37/0.96  --sat_out_model                         small
% 2.37/0.96  --sat_out_clauses                       false
% 2.37/0.96  
% 2.37/0.96  ------ QBF Options
% 2.37/0.96  
% 2.37/0.96  --qbf_mode                              false
% 2.37/0.96  --qbf_elim_univ                         false
% 2.37/0.96  --qbf_dom_inst                          none
% 2.37/0.96  --qbf_dom_pre_inst                      false
% 2.37/0.96  --qbf_sk_in                             false
% 2.37/0.96  --qbf_pred_elim                         true
% 2.37/0.96  --qbf_split                             512
% 2.37/0.96  
% 2.37/0.96  ------ BMC1 Options
% 2.37/0.96  
% 2.37/0.96  --bmc1_incremental                      false
% 2.37/0.96  --bmc1_axioms                           reachable_all
% 2.37/0.96  --bmc1_min_bound                        0
% 2.37/0.96  --bmc1_max_bound                        -1
% 2.37/0.96  --bmc1_max_bound_default                -1
% 2.37/0.96  --bmc1_symbol_reachability              true
% 2.37/0.96  --bmc1_property_lemmas                  false
% 2.37/0.96  --bmc1_k_induction                      false
% 2.37/0.96  --bmc1_non_equiv_states                 false
% 2.37/0.96  --bmc1_deadlock                         false
% 2.37/0.96  --bmc1_ucm                              false
% 2.37/0.96  --bmc1_add_unsat_core                   none
% 2.37/0.96  --bmc1_unsat_core_children              false
% 2.37/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/0.96  --bmc1_out_stat                         full
% 2.37/0.96  --bmc1_ground_init                      false
% 2.37/0.96  --bmc1_pre_inst_next_state              false
% 2.37/0.96  --bmc1_pre_inst_state                   false
% 2.37/0.96  --bmc1_pre_inst_reach_state             false
% 2.37/0.96  --bmc1_out_unsat_core                   false
% 2.37/0.96  --bmc1_aig_witness_out                  false
% 2.37/0.96  --bmc1_verbose                          false
% 2.37/0.96  --bmc1_dump_clauses_tptp                false
% 2.37/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.37/0.96  --bmc1_dump_file                        -
% 2.37/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.37/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.37/0.96  --bmc1_ucm_extend_mode                  1
% 2.37/0.96  --bmc1_ucm_init_mode                    2
% 2.37/0.96  --bmc1_ucm_cone_mode                    none
% 2.37/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.37/0.96  --bmc1_ucm_relax_model                  4
% 2.37/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.37/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/0.96  --bmc1_ucm_layered_model                none
% 2.37/0.96  --bmc1_ucm_max_lemma_size               10
% 2.37/0.96  
% 2.37/0.96  ------ AIG Options
% 2.37/0.96  
% 2.37/0.96  --aig_mode                              false
% 2.37/0.96  
% 2.37/0.96  ------ Instantiation Options
% 2.37/0.96  
% 2.37/0.96  --instantiation_flag                    true
% 2.37/0.96  --inst_sos_flag                         false
% 2.37/0.96  --inst_sos_phase                        true
% 2.37/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/0.96  --inst_lit_sel_side                     num_symb
% 2.37/0.96  --inst_solver_per_active                1400
% 2.37/0.96  --inst_solver_calls_frac                1.
% 2.37/0.96  --inst_passive_queue_type               priority_queues
% 2.37/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/0.96  --inst_passive_queues_freq              [25;2]
% 2.37/0.96  --inst_dismatching                      true
% 2.37/0.96  --inst_eager_unprocessed_to_passive     true
% 2.37/0.96  --inst_prop_sim_given                   true
% 2.37/0.96  --inst_prop_sim_new                     false
% 2.37/0.96  --inst_subs_new                         false
% 2.37/0.96  --inst_eq_res_simp                      false
% 2.37/0.96  --inst_subs_given                       false
% 2.37/0.96  --inst_orphan_elimination               true
% 2.37/0.96  --inst_learning_loop_flag               true
% 2.37/0.96  --inst_learning_start                   3000
% 2.37/0.96  --inst_learning_factor                  2
% 2.37/0.96  --inst_start_prop_sim_after_learn       3
% 2.37/0.96  --inst_sel_renew                        solver
% 2.37/0.96  --inst_lit_activity_flag                true
% 2.37/0.96  --inst_restr_to_given                   false
% 2.37/0.96  --inst_activity_threshold               500
% 2.37/0.96  --inst_out_proof                        true
% 2.37/0.96  
% 2.37/0.96  ------ Resolution Options
% 2.37/0.96  
% 2.37/0.96  --resolution_flag                       true
% 2.37/0.96  --res_lit_sel                           adaptive
% 2.37/0.96  --res_lit_sel_side                      none
% 2.37/0.96  --res_ordering                          kbo
% 2.37/0.96  --res_to_prop_solver                    active
% 2.37/0.96  --res_prop_simpl_new                    false
% 2.37/0.96  --res_prop_simpl_given                  true
% 2.37/0.96  --res_passive_queue_type                priority_queues
% 2.37/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/0.96  --res_passive_queues_freq               [15;5]
% 2.37/0.96  --res_forward_subs                      full
% 2.37/0.96  --res_backward_subs                     full
% 2.37/0.96  --res_forward_subs_resolution           true
% 2.37/0.96  --res_backward_subs_resolution          true
% 2.37/0.96  --res_orphan_elimination                true
% 2.37/0.96  --res_time_limit                        2.
% 2.37/0.96  --res_out_proof                         true
% 2.37/0.96  
% 2.37/0.96  ------ Superposition Options
% 2.37/0.96  
% 2.37/0.96  --superposition_flag                    true
% 2.37/0.96  --sup_passive_queue_type                priority_queues
% 2.37/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.37/0.96  --demod_completeness_check              fast
% 2.37/0.96  --demod_use_ground                      true
% 2.37/0.96  --sup_to_prop_solver                    passive
% 2.37/0.96  --sup_prop_simpl_new                    true
% 2.37/0.96  --sup_prop_simpl_given                  true
% 2.37/0.96  --sup_fun_splitting                     false
% 2.37/0.96  --sup_smt_interval                      50000
% 2.37/0.96  
% 2.37/0.96  ------ Superposition Simplification Setup
% 2.37/0.96  
% 2.37/0.96  --sup_indices_passive                   []
% 2.37/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.96  --sup_full_bw                           [BwDemod]
% 2.37/0.96  --sup_immed_triv                        [TrivRules]
% 2.37/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.96  --sup_immed_bw_main                     []
% 2.37/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.96  
% 2.37/0.96  ------ Combination Options
% 2.37/0.96  
% 2.37/0.96  --comb_res_mult                         3
% 2.37/0.96  --comb_sup_mult                         2
% 2.37/0.96  --comb_inst_mult                        10
% 2.37/0.96  
% 2.37/0.96  ------ Debug Options
% 2.37/0.96  
% 2.37/0.96  --dbg_backtrace                         false
% 2.37/0.96  --dbg_dump_prop_clauses                 false
% 2.37/0.96  --dbg_dump_prop_clauses_file            -
% 2.37/0.96  --dbg_out_stat                          false
% 2.37/0.96  ------ Parsing...
% 2.37/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.37/0.96  
% 2.37/0.96  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.37/0.96  
% 2.37/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.37/0.96  
% 2.37/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.37/0.96  ------ Proving...
% 2.37/0.96  ------ Problem Properties 
% 2.37/0.96  
% 2.37/0.96  
% 2.37/0.96  clauses                                 18
% 2.37/0.96  conjectures                             2
% 2.37/0.96  EPR                                     3
% 2.37/0.96  Horn                                    15
% 2.37/0.96  unary                                   4
% 2.37/0.96  binary                                  6
% 2.37/0.96  lits                                    44
% 2.37/0.96  lits eq                                 26
% 2.37/0.96  fd_pure                                 0
% 2.37/0.96  fd_pseudo                               0
% 2.37/0.96  fd_cond                                 2
% 2.37/0.96  fd_pseudo_cond                          0
% 2.37/0.96  AC symbols                              0
% 2.37/0.96  
% 2.37/0.96  ------ Schedule dynamic 5 is on 
% 2.37/0.96  
% 2.37/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.37/0.96  
% 2.37/0.96  
% 2.37/0.96  ------ 
% 2.37/0.96  Current options:
% 2.37/0.96  ------ 
% 2.37/0.96  
% 2.37/0.96  ------ Input Options
% 2.37/0.96  
% 2.37/0.96  --out_options                           all
% 2.37/0.96  --tptp_safe_out                         true
% 2.37/0.96  --problem_path                          ""
% 2.37/0.96  --include_path                          ""
% 2.37/0.96  --clausifier                            res/vclausify_rel
% 2.37/0.96  --clausifier_options                    --mode clausify
% 2.37/0.96  --stdin                                 false
% 2.37/0.96  --stats_out                             all
% 2.37/0.96  
% 2.37/0.96  ------ General Options
% 2.37/0.96  
% 2.37/0.96  --fof                                   false
% 2.37/0.96  --time_out_real                         305.
% 2.37/0.96  --time_out_virtual                      -1.
% 2.37/0.96  --symbol_type_check                     false
% 2.37/0.96  --clausify_out                          false
% 2.37/0.96  --sig_cnt_out                           false
% 2.37/0.96  --trig_cnt_out                          false
% 2.37/0.96  --trig_cnt_out_tolerance                1.
% 2.37/0.96  --trig_cnt_out_sk_spl                   false
% 2.37/0.96  --abstr_cl_out                          false
% 2.37/0.96  
% 2.37/0.96  ------ Global Options
% 2.37/0.96  
% 2.37/0.96  --schedule                              default
% 2.37/0.96  --add_important_lit                     false
% 2.37/0.96  --prop_solver_per_cl                    1000
% 2.37/0.96  --min_unsat_core                        false
% 2.37/0.96  --soft_assumptions                      false
% 2.37/0.96  --soft_lemma_size                       3
% 2.37/0.96  --prop_impl_unit_size                   0
% 2.37/0.96  --prop_impl_unit                        []
% 2.37/0.96  --share_sel_clauses                     true
% 2.37/0.96  --reset_solvers                         false
% 2.37/0.96  --bc_imp_inh                            [conj_cone]
% 2.37/0.96  --conj_cone_tolerance                   3.
% 2.37/0.96  --extra_neg_conj                        none
% 2.37/0.96  --large_theory_mode                     true
% 2.37/0.96  --prolific_symb_bound                   200
% 2.37/0.96  --lt_threshold                          2000
% 2.37/0.96  --clause_weak_htbl                      true
% 2.37/0.96  --gc_record_bc_elim                     false
% 2.37/0.96  
% 2.37/0.96  ------ Preprocessing Options
% 2.37/0.96  
% 2.37/0.96  --preprocessing_flag                    true
% 2.37/0.96  --time_out_prep_mult                    0.1
% 2.37/0.96  --splitting_mode                        input
% 2.37/0.96  --splitting_grd                         true
% 2.37/0.96  --splitting_cvd                         false
% 2.37/0.96  --splitting_cvd_svl                     false
% 2.37/0.96  --splitting_nvd                         32
% 2.37/0.96  --sub_typing                            true
% 2.37/0.96  --prep_gs_sim                           true
% 2.37/0.96  --prep_unflatten                        true
% 2.37/0.96  --prep_res_sim                          true
% 2.37/0.96  --prep_upred                            true
% 2.37/0.96  --prep_sem_filter                       exhaustive
% 2.37/0.96  --prep_sem_filter_out                   false
% 2.37/0.96  --pred_elim                             true
% 2.37/0.96  --res_sim_input                         true
% 2.37/0.96  --eq_ax_congr_red                       true
% 2.37/0.96  --pure_diseq_elim                       true
% 2.37/0.96  --brand_transform                       false
% 2.37/0.96  --non_eq_to_eq                          false
% 2.37/0.96  --prep_def_merge                        true
% 2.37/0.96  --prep_def_merge_prop_impl              false
% 2.37/0.96  --prep_def_merge_mbd                    true
% 2.37/0.96  --prep_def_merge_tr_red                 false
% 2.37/0.96  --prep_def_merge_tr_cl                  false
% 2.37/0.96  --smt_preprocessing                     true
% 2.37/0.96  --smt_ac_axioms                         fast
% 2.37/0.96  --preprocessed_out                      false
% 2.37/0.96  --preprocessed_stats                    false
% 2.37/0.96  
% 2.37/0.96  ------ Abstraction refinement Options
% 2.37/0.96  
% 2.37/0.96  --abstr_ref                             []
% 2.37/0.96  --abstr_ref_prep                        false
% 2.37/0.96  --abstr_ref_until_sat                   false
% 2.37/0.96  --abstr_ref_sig_restrict                funpre
% 2.37/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/0.96  --abstr_ref_under                       []
% 2.37/0.96  
% 2.37/0.96  ------ SAT Options
% 2.37/0.96  
% 2.37/0.96  --sat_mode                              false
% 2.37/0.96  --sat_fm_restart_options                ""
% 2.37/0.96  --sat_gr_def                            false
% 2.37/0.96  --sat_epr_types                         true
% 2.37/0.96  --sat_non_cyclic_types                  false
% 2.37/0.96  --sat_finite_models                     false
% 2.37/0.96  --sat_fm_lemmas                         false
% 2.37/0.96  --sat_fm_prep                           false
% 2.37/0.96  --sat_fm_uc_incr                        true
% 2.37/0.96  --sat_out_model                         small
% 2.37/0.96  --sat_out_clauses                       false
% 2.37/0.96  
% 2.37/0.96  ------ QBF Options
% 2.37/0.96  
% 2.37/0.96  --qbf_mode                              false
% 2.37/0.96  --qbf_elim_univ                         false
% 2.37/0.96  --qbf_dom_inst                          none
% 2.37/0.96  --qbf_dom_pre_inst                      false
% 2.37/0.96  --qbf_sk_in                             false
% 2.37/0.96  --qbf_pred_elim                         true
% 2.37/0.96  --qbf_split                             512
% 2.37/0.96  
% 2.37/0.96  ------ BMC1 Options
% 2.37/0.96  
% 2.37/0.96  --bmc1_incremental                      false
% 2.37/0.96  --bmc1_axioms                           reachable_all
% 2.37/0.96  --bmc1_min_bound                        0
% 2.37/0.96  --bmc1_max_bound                        -1
% 2.37/0.96  --bmc1_max_bound_default                -1
% 2.37/0.96  --bmc1_symbol_reachability              true
% 2.37/0.96  --bmc1_property_lemmas                  false
% 2.37/0.96  --bmc1_k_induction                      false
% 2.37/0.96  --bmc1_non_equiv_states                 false
% 2.37/0.96  --bmc1_deadlock                         false
% 2.37/0.96  --bmc1_ucm                              false
% 2.37/0.96  --bmc1_add_unsat_core                   none
% 2.37/0.96  --bmc1_unsat_core_children              false
% 2.37/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/0.96  --bmc1_out_stat                         full
% 2.37/0.96  --bmc1_ground_init                      false
% 2.37/0.96  --bmc1_pre_inst_next_state              false
% 2.37/0.96  --bmc1_pre_inst_state                   false
% 2.37/0.96  --bmc1_pre_inst_reach_state             false
% 2.37/0.96  --bmc1_out_unsat_core                   false
% 2.37/0.96  --bmc1_aig_witness_out                  false
% 2.37/0.96  --bmc1_verbose                          false
% 2.37/0.96  --bmc1_dump_clauses_tptp                false
% 2.37/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.37/0.96  --bmc1_dump_file                        -
% 2.37/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.37/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.37/0.96  --bmc1_ucm_extend_mode                  1
% 2.37/0.96  --bmc1_ucm_init_mode                    2
% 2.37/0.96  --bmc1_ucm_cone_mode                    none
% 2.37/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.37/0.96  --bmc1_ucm_relax_model                  4
% 2.37/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.37/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/0.96  --bmc1_ucm_layered_model                none
% 2.37/0.96  --bmc1_ucm_max_lemma_size               10
% 2.37/0.96  
% 2.37/0.96  ------ AIG Options
% 2.37/0.96  
% 2.37/0.96  --aig_mode                              false
% 2.37/0.96  
% 2.37/0.96  ------ Instantiation Options
% 2.37/0.96  
% 2.37/0.96  --instantiation_flag                    true
% 2.37/0.96  --inst_sos_flag                         false
% 2.37/0.96  --inst_sos_phase                        true
% 2.37/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/0.96  --inst_lit_sel_side                     none
% 2.37/0.96  --inst_solver_per_active                1400
% 2.37/0.96  --inst_solver_calls_frac                1.
% 2.37/0.96  --inst_passive_queue_type               priority_queues
% 2.37/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/0.96  --inst_passive_queues_freq              [25;2]
% 2.37/0.96  --inst_dismatching                      true
% 2.37/0.96  --inst_eager_unprocessed_to_passive     true
% 2.37/0.96  --inst_prop_sim_given                   true
% 2.37/0.96  --inst_prop_sim_new                     false
% 2.37/0.96  --inst_subs_new                         false
% 2.37/0.96  --inst_eq_res_simp                      false
% 2.37/0.96  --inst_subs_given                       false
% 2.37/0.96  --inst_orphan_elimination               true
% 2.37/0.96  --inst_learning_loop_flag               true
% 2.37/0.96  --inst_learning_start                   3000
% 2.37/0.96  --inst_learning_factor                  2
% 2.37/0.96  --inst_start_prop_sim_after_learn       3
% 2.37/0.96  --inst_sel_renew                        solver
% 2.37/0.96  --inst_lit_activity_flag                true
% 2.37/0.96  --inst_restr_to_given                   false
% 2.37/0.96  --inst_activity_threshold               500
% 2.37/0.96  --inst_out_proof                        true
% 2.37/0.96  
% 2.37/0.96  ------ Resolution Options
% 2.37/0.96  
% 2.37/0.96  --resolution_flag                       false
% 2.37/0.96  --res_lit_sel                           adaptive
% 2.37/0.96  --res_lit_sel_side                      none
% 2.37/0.96  --res_ordering                          kbo
% 2.37/0.96  --res_to_prop_solver                    active
% 2.37/0.96  --res_prop_simpl_new                    false
% 2.37/0.96  --res_prop_simpl_given                  true
% 2.37/0.96  --res_passive_queue_type                priority_queues
% 2.37/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/0.96  --res_passive_queues_freq               [15;5]
% 2.37/0.96  --res_forward_subs                      full
% 2.37/0.96  --res_backward_subs                     full
% 2.37/0.96  --res_forward_subs_resolution           true
% 2.37/0.96  --res_backward_subs_resolution          true
% 2.37/0.96  --res_orphan_elimination                true
% 2.37/0.96  --res_time_limit                        2.
% 2.37/0.96  --res_out_proof                         true
% 2.37/0.96  
% 2.37/0.96  ------ Superposition Options
% 2.37/0.96  
% 2.37/0.96  --superposition_flag                    true
% 2.37/0.96  --sup_passive_queue_type                priority_queues
% 2.37/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.37/0.96  --demod_completeness_check              fast
% 2.37/0.96  --demod_use_ground                      true
% 2.37/0.96  --sup_to_prop_solver                    passive
% 2.37/0.96  --sup_prop_simpl_new                    true
% 2.37/0.96  --sup_prop_simpl_given                  true
% 2.37/0.96  --sup_fun_splitting                     false
% 2.37/0.96  --sup_smt_interval                      50000
% 2.37/0.96  
% 2.37/0.96  ------ Superposition Simplification Setup
% 2.37/0.96  
% 2.37/0.96  --sup_indices_passive                   []
% 2.37/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.96  --sup_full_bw                           [BwDemod]
% 2.37/0.96  --sup_immed_triv                        [TrivRules]
% 2.37/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.96  --sup_immed_bw_main                     []
% 2.37/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.96  
% 2.37/0.96  ------ Combination Options
% 2.37/0.96  
% 2.37/0.96  --comb_res_mult                         3
% 2.37/0.96  --comb_sup_mult                         2
% 2.37/0.96  --comb_inst_mult                        10
% 2.37/0.96  
% 2.37/0.96  ------ Debug Options
% 2.37/0.96  
% 2.37/0.96  --dbg_backtrace                         false
% 2.37/0.96  --dbg_dump_prop_clauses                 false
% 2.37/0.96  --dbg_dump_prop_clauses_file            -
% 2.37/0.96  --dbg_out_stat                          false
% 2.37/0.96  
% 2.37/0.96  
% 2.37/0.96  
% 2.37/0.96  
% 2.37/0.96  ------ Proving...
% 2.37/0.96  
% 2.37/0.96  
% 2.37/0.96  % SZS status Theorem for theBenchmark.p
% 2.37/0.96  
% 2.37/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.37/0.96  
% 2.37/0.96  fof(f8,axiom,(
% 2.37/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f17,plain,(
% 2.37/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.37/0.96    inference(ennf_transformation,[],[f8])).
% 2.37/0.96  
% 2.37/0.96  fof(f18,plain,(
% 2.37/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.37/0.96    inference(flattening,[],[f17])).
% 2.37/0.96  
% 2.37/0.96  fof(f23,plain,(
% 2.37/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.37/0.96    inference(nnf_transformation,[],[f18])).
% 2.37/0.96  
% 2.37/0.96  fof(f35,plain,(
% 2.37/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f23])).
% 2.37/0.96  
% 2.37/0.96  fof(f9,conjecture,(
% 2.37/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f10,negated_conjecture,(
% 2.37/0.96    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.37/0.96    inference(negated_conjecture,[],[f9])).
% 2.37/0.96  
% 2.37/0.96  fof(f19,plain,(
% 2.37/0.96    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.37/0.96    inference(ennf_transformation,[],[f10])).
% 2.37/0.96  
% 2.37/0.96  fof(f20,plain,(
% 2.37/0.96    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.37/0.96    inference(flattening,[],[f19])).
% 2.37/0.96  
% 2.37/0.96  fof(f24,plain,(
% 2.37/0.96    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.37/0.96    introduced(choice_axiom,[])).
% 2.37/0.96  
% 2.37/0.96  fof(f25,plain,(
% 2.37/0.96    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.37/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).
% 2.37/0.96  
% 2.37/0.96  fof(f42,plain,(
% 2.37/0.96    v1_funct_2(sK3,sK0,sK1)),
% 2.37/0.96    inference(cnf_transformation,[],[f25])).
% 2.37/0.96  
% 2.37/0.96  fof(f43,plain,(
% 2.37/0.96    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.37/0.96    inference(cnf_transformation,[],[f25])).
% 2.37/0.96  
% 2.37/0.96  fof(f5,axiom,(
% 2.37/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f13,plain,(
% 2.37/0.96    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.37/0.96    inference(ennf_transformation,[],[f5])).
% 2.37/0.96  
% 2.37/0.96  fof(f32,plain,(
% 2.37/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f13])).
% 2.37/0.96  
% 2.37/0.96  fof(f6,axiom,(
% 2.37/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f14,plain,(
% 2.37/0.96    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.37/0.96    inference(ennf_transformation,[],[f6])).
% 2.37/0.96  
% 2.37/0.96  fof(f33,plain,(
% 2.37/0.96    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f14])).
% 2.37/0.96  
% 2.37/0.96  fof(f7,axiom,(
% 2.37/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f15,plain,(
% 2.37/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.37/0.96    inference(ennf_transformation,[],[f7])).
% 2.37/0.96  
% 2.37/0.96  fof(f16,plain,(
% 2.37/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.37/0.96    inference(flattening,[],[f15])).
% 2.37/0.96  
% 2.37/0.96  fof(f34,plain,(
% 2.37/0.96    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f16])).
% 2.37/0.96  
% 2.37/0.96  fof(f44,plain,(
% 2.37/0.96    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 2.37/0.96    inference(cnf_transformation,[],[f25])).
% 2.37/0.96  
% 2.37/0.96  fof(f37,plain,(
% 2.37/0.96    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f23])).
% 2.37/0.96  
% 2.37/0.96  fof(f46,plain,(
% 2.37/0.96    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.37/0.96    inference(cnf_transformation,[],[f25])).
% 2.37/0.96  
% 2.37/0.96  fof(f41,plain,(
% 2.37/0.96    v1_funct_1(sK3)),
% 2.37/0.96    inference(cnf_transformation,[],[f25])).
% 2.37/0.96  
% 2.37/0.96  fof(f3,axiom,(
% 2.37/0.96    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f21,plain,(
% 2.37/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.37/0.96    inference(nnf_transformation,[],[f3])).
% 2.37/0.96  
% 2.37/0.96  fof(f22,plain,(
% 2.37/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.37/0.96    inference(flattening,[],[f21])).
% 2.37/0.96  
% 2.37/0.96  fof(f30,plain,(
% 2.37/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.37/0.96    inference(cnf_transformation,[],[f22])).
% 2.37/0.96  
% 2.37/0.96  fof(f47,plain,(
% 2.37/0.96    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.37/0.96    inference(equality_resolution,[],[f30])).
% 2.37/0.96  
% 2.37/0.96  fof(f29,plain,(
% 2.37/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.37/0.96    inference(cnf_transformation,[],[f22])).
% 2.37/0.96  
% 2.37/0.96  fof(f48,plain,(
% 2.37/0.96    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.37/0.96    inference(equality_resolution,[],[f29])).
% 2.37/0.96  
% 2.37/0.96  fof(f1,axiom,(
% 2.37/0.96    v1_xboole_0(k1_xboole_0)),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f26,plain,(
% 2.37/0.96    v1_xboole_0(k1_xboole_0)),
% 2.37/0.96    inference(cnf_transformation,[],[f1])).
% 2.37/0.96  
% 2.37/0.96  fof(f45,plain,(
% 2.37/0.96    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.37/0.96    inference(cnf_transformation,[],[f25])).
% 2.37/0.96  
% 2.37/0.96  fof(f2,axiom,(
% 2.37/0.96    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f11,plain,(
% 2.37/0.96    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.37/0.96    inference(ennf_transformation,[],[f2])).
% 2.37/0.96  
% 2.37/0.96  fof(f27,plain,(
% 2.37/0.96    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.37/0.96    inference(cnf_transformation,[],[f11])).
% 2.37/0.96  
% 2.37/0.96  fof(f4,axiom,(
% 2.37/0.96    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.37/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.96  
% 2.37/0.96  fof(f12,plain,(
% 2.37/0.96    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.37/0.96    inference(ennf_transformation,[],[f4])).
% 2.37/0.96  
% 2.37/0.96  fof(f31,plain,(
% 2.37/0.96    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.37/0.96    inference(cnf_transformation,[],[f12])).
% 2.37/0.96  
% 2.37/0.96  fof(f38,plain,(
% 2.37/0.96    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f23])).
% 2.37/0.96  
% 2.37/0.96  fof(f52,plain,(
% 2.37/0.96    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.37/0.96    inference(equality_resolution,[],[f38])).
% 2.37/0.96  
% 2.37/0.96  fof(f36,plain,(
% 2.37/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f23])).
% 2.37/0.96  
% 2.37/0.96  fof(f53,plain,(
% 2.37/0.96    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.37/0.96    inference(equality_resolution,[],[f36])).
% 2.37/0.96  
% 2.37/0.96  fof(f40,plain,(
% 2.37/0.96    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(cnf_transformation,[],[f23])).
% 2.37/0.96  
% 2.37/0.96  fof(f49,plain,(
% 2.37/0.96    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.37/0.96    inference(equality_resolution,[],[f40])).
% 2.37/0.96  
% 2.37/0.96  fof(f50,plain,(
% 2.37/0.96    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.37/0.96    inference(equality_resolution,[],[f49])).
% 2.37/0.96  
% 2.37/0.96  cnf(c_14,plain,
% 2.37/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.37/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.37/0.96      | k1_xboole_0 = X2 ),
% 2.37/0.96      inference(cnf_transformation,[],[f35]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_19,negated_conjecture,
% 2.37/0.96      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.37/0.96      inference(cnf_transformation,[],[f42]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_308,plain,
% 2.37/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.37/0.96      | sK1 != X2
% 2.37/0.96      | sK0 != X1
% 2.37/0.96      | sK3 != X0
% 2.37/0.96      | k1_xboole_0 = X2 ),
% 2.37/0.96      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_309,plain,
% 2.37/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.37/0.96      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.37/0.96      | k1_xboole_0 = sK1 ),
% 2.37/0.96      inference(unflattening,[status(thm)],[c_308]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_18,negated_conjecture,
% 2.37/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.37/0.96      inference(cnf_transformation,[],[f43]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_311,plain,
% 2.37/0.96      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.37/0.96      inference(global_propositional_subsumption,
% 2.37/0.96                [status(thm)],
% 2.37/0.96                [c_309,c_18]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_697,plain,
% 2.37/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.37/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_6,plain,
% 2.37/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.37/0.96      inference(cnf_transformation,[],[f32]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_699,plain,
% 2.37/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.37/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.37/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1423,plain,
% 2.37/0.96      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.37/0.96      inference(superposition,[status(thm)],[c_697,c_699]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1501,plain,
% 2.37/0.96      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.37/0.96      inference(superposition,[status(thm)],[c_311,c_1423]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_7,plain,
% 2.37/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.37/0.96      inference(cnf_transformation,[],[f33]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_698,plain,
% 2.37/0.96      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.37/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.37/0.96      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1215,plain,
% 2.37/0.96      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.37/0.96      inference(superposition,[status(thm)],[c_697,c_698]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_8,plain,
% 2.37/0.96      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.37/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.37/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.37/0.96      inference(cnf_transformation,[],[f34]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_17,negated_conjecture,
% 2.37/0.96      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 2.37/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_196,plain,
% 2.37/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.37/0.96      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
% 2.37/0.96      | sK2 != X3 ),
% 2.37/0.96      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_197,plain,
% 2.37/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 2.37/0.96      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0) ),
% 2.37/0.96      inference(unflattening,[status(thm)],[c_196]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_696,plain,
% 2.37/0.96      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(X0)
% 2.37/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.37/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) = iProver_top ),
% 2.37/0.96      inference(predicate_to_equality,[status(thm)],[c_197]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1261,plain,
% 2.37/0.96      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.37/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.37/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) = iProver_top ),
% 2.37/0.96      inference(demodulation,[status(thm)],[c_1215,c_696]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1269,plain,
% 2.37/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top ),
% 2.37/0.96      inference(equality_resolution,[status(thm)],[c_1261]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1537,plain,
% 2.37/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.37/0.96      inference(superposition,[status(thm)],[c_697,c_1269]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1556,plain,
% 2.37/0.96      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.37/0.96      inference(superposition,[status(thm)],[c_1537,c_699]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_12,plain,
% 2.37/0.96      ( v1_funct_2(X0,X1,X2)
% 2.37/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | k1_relset_1(X1,X2,X0) != X1
% 2.37/0.96      | k1_xboole_0 = X2 ),
% 2.37/0.96      inference(cnf_transformation,[],[f37]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_15,negated_conjecture,
% 2.37/0.96      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.37/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.96      | ~ v1_funct_1(sK3) ),
% 2.37/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_20,negated_conjecture,
% 2.37/0.96      ( v1_funct_1(sK3) ),
% 2.37/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_97,plain,
% 2.37/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.96      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.37/0.96      inference(global_propositional_subsumption,
% 2.37/0.96                [status(thm)],
% 2.37/0.96                [c_15,c_20]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_98,negated_conjecture,
% 2.37/0.96      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.37/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.37/0.96      inference(renaming,[status(thm)],[c_97]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_295,plain,
% 2.37/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.37/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.96      | k1_relset_1(X1,X2,X0) != X1
% 2.37/0.96      | sK2 != X2
% 2.37/0.96      | sK0 != X1
% 2.37/0.96      | sK3 != X0
% 2.37/0.96      | k1_xboole_0 = X2 ),
% 2.37/0.96      inference(resolution_lifted,[status(thm)],[c_12,c_98]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_296,plain,
% 2.37/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.96      | k1_relset_1(sK0,sK2,sK3) != sK0
% 2.37/0.96      | k1_xboole_0 = sK2 ),
% 2.37/0.96      inference(unflattening,[status(thm)],[c_295]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_691,plain,
% 2.37/0.96      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 2.37/0.96      | k1_xboole_0 = sK2
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.37/0.96      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1639,plain,
% 2.37/0.96      ( k1_relat_1(sK3) != sK0
% 2.37/0.96      | sK2 = k1_xboole_0
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.37/0.96      inference(demodulation,[status(thm)],[c_1556,c_691]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_23,plain,
% 2.37/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.37/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_841,plain,
% 2.37/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.37/0.96      | k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.37/0.96      inference(instantiation,[status(thm)],[c_7]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_849,plain,
% 2.37/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 2.37/0.96      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
% 2.37/0.96      inference(instantiation,[status(thm)],[c_197]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_940,plain,
% 2.37/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.96      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) ),
% 2.37/0.96      inference(instantiation,[status(thm)],[c_849]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_941,plain,
% 2.37/0.96      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.37/0.96      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1691,plain,
% 2.37/0.96      ( sK2 = k1_xboole_0 | k1_relat_1(sK3) != sK0 ),
% 2.37/0.96      inference(global_propositional_subsumption,
% 2.37/0.96                [status(thm)],
% 2.37/0.96                [c_1639,c_18,c_23,c_841,c_941]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1692,plain,
% 2.37/0.96      ( k1_relat_1(sK3) != sK0 | sK2 = k1_xboole_0 ),
% 2.37/0.96      inference(renaming,[status(thm)],[c_1691]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1695,plain,
% 2.37/0.96      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.37/0.96      inference(superposition,[status(thm)],[c_1501,c_1692]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1824,plain,
% 2.37/0.96      ( sK2 = k1_xboole_0
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.37/0.96      inference(superposition,[status(thm)],[c_1695,c_697]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_2,plain,
% 2.37/0.96      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.37/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.37/0.96  
% 2.37/0.96  cnf(c_1832,plain,
% 2.37/0.96      ( sK2 = k1_xboole_0
% 2.37/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_1824,c_2]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_3,plain,
% 2.37/0.97      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.37/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_53,plain,
% 2.37/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_0,plain,
% 2.37/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.37/0.97      inference(cnf_transformation,[],[f26]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_458,plain,( X0 = X0 ),theory(equality) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_862,plain,
% 2.37/0.97      ( sK3 = sK3 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_458]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_460,plain,
% 2.37/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.37/0.97      theory(equality) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1124,plain,
% 2.37/0.97      ( ~ v1_xboole_0(X0)
% 2.37/0.97      | v1_xboole_0(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | k2_zfmisc_1(sK0,sK2) != X0 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_460]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1572,plain,
% 2.37/0.97      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
% 2.37/0.97      | v1_xboole_0(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(X0,X1) ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1124]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1575,plain,
% 2.37/0.97      ( v1_xboole_0(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.37/0.97      | k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1572]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_461,plain,
% 2.37/0.97      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 2.37/0.97      theory(equality) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1573,plain,
% 2.37/0.97      ( k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(X0,X1)
% 2.37/0.97      | sK2 != X1
% 2.37/0.97      | sK0 != X0 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_461]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1578,plain,
% 2.37/0.97      ( k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 2.37/0.97      | sK2 != k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1573]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_463,plain,
% 2.37/0.97      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.37/0.97      theory(equality) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1013,plain,
% 2.37/0.97      ( m1_subset_1(X0,X1)
% 2.37/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.97      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | X0 != sK3 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_463]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1170,plain,
% 2.37/0.97      ( m1_subset_1(sK3,X0)
% 2.37/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.97      | X0 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | sK3 != sK3 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1013]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1593,plain,
% 2.37/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(X0))
% 2.37/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.97      | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | sK3 != sK3 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1170]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1595,plain,
% 2.37/0.97      ( k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | sK3 != sK3
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_1593]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1597,plain,
% 2.37/0.97      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | sK3 != sK3
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1595]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_462,plain,
% 2.37/0.97      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.37/0.97      theory(equality) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1594,plain,
% 2.37/0.97      ( X0 != k2_zfmisc_1(sK0,sK2)
% 2.37/0.97      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_462]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1599,plain,
% 2.37/0.97      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | k1_xboole_0 != k2_zfmisc_1(sK0,sK2) ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1594]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1672,plain,
% 2.37/0.97      ( ~ v1_xboole_0(X0)
% 2.37/0.97      | v1_xboole_0(k2_zfmisc_1(X1,X2))
% 2.37/0.97      | k2_zfmisc_1(X1,X2) != X0 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_460]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1674,plain,
% 2.37/0.97      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.37/0.97      | ~ v1_xboole_0(k1_xboole_0)
% 2.37/0.97      | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1672]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_16,negated_conjecture,
% 2.37/0.97      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.37/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1825,plain,
% 2.37/0.97      ( sK2 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_1695,c_16]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1915,plain,
% 2.37/0.97      ( sK0 = k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_1825,c_1537]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1926,plain,
% 2.37/0.97      ( sK0 = k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_1915,c_2]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1,plain,
% 2.37/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.37/0.97      inference(cnf_transformation,[],[f27]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2018,plain,
% 2.37/0.97      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK2))
% 2.37/0.97      | k1_xboole_0 = k2_zfmisc_1(sK0,sK2) ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2132,plain,
% 2.37/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.37/0.97      inference(global_propositional_subsumption,
% 2.37/0.97                [status(thm)],
% 2.37/0.97                [c_1832,c_18,c_23,c_53,c_0,c_841,c_862,c_941,c_1575,
% 2.37/0.97                 c_1578,c_1597,c_1599,c_1674,c_1926,c_2018]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1538,plain,
% 2.37/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_2,c_1269]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_5,plain,
% 2.37/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.37/0.97      | ~ v1_xboole_0(X1)
% 2.37/0.97      | v1_xboole_0(X0) ),
% 2.37/0.97      inference(cnf_transformation,[],[f31]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_700,plain,
% 2.37/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.37/0.97      | v1_xboole_0(X1) != iProver_top
% 2.37/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1724,plain,
% 2.37/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.37/0.97      | v1_xboole_0(k2_zfmisc_1(X0,sK2)) != iProver_top
% 2.37/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_1538,c_700]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_57,plain,
% 2.37/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_892,plain,
% 2.37/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 2.37/0.97      | ~ v1_xboole_0(X0)
% 2.37/0.97      | v1_xboole_0(sK3) ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_893,plain,
% 2.37/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 2.37/0.97      | v1_xboole_0(X0) != iProver_top
% 2.37/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_892]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_895,plain,
% 2.37/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.37/0.97      | v1_xboole_0(sK3) = iProver_top
% 2.37/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_893]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1810,plain,
% 2.37/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.37/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 2.37/0.97      inference(global_propositional_subsumption,
% 2.37/0.97                [status(thm)],
% 2.37/0.97                [c_1724,c_57,c_895]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2138,plain,
% 2.37/0.97      ( v1_xboole_0(sK3) = iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_2132,c_1810]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_701,plain,
% 2.37/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2369,plain,
% 2.37/0.97      ( sK3 = k1_xboole_0 ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_2138,c_701]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2716,plain,
% 2.37/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_2369,c_2132]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1425,plain,
% 2.37/0.97      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.37/0.97      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_3,c_699]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2141,plain,
% 2.37/0.97      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_2132,c_1425]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_11,plain,
% 2.37/0.97      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.37/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.37/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.37/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_266,plain,
% 2.37/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.37/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.37/0.97      | sK2 != X1
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | sK3 != X0 ),
% 2.37/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_98]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_267,plain,
% 2.37/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.37/0.97      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0 ),
% 2.37/0.97      inference(unflattening,[status(thm)],[c_266]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_693,plain,
% 2.37/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_775,plain,
% 2.37/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_693,c_3]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2282,plain,
% 2.37/0.97      ( k1_relat_1(sK3) != k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_2141,c_775]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_13,plain,
% 2.37/0.97      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.37/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.37/0.97      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.37/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_282,plain,
% 2.37/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.37/0.97      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.37/0.97      | sK1 != X1
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | sK3 != X0 ),
% 2.37/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_283,plain,
% 2.37/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.37/0.97      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0 ),
% 2.37/0.97      inference(unflattening,[status(thm)],[c_282]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_692,plain,
% 2.37/0.97      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_753,plain,
% 2.37/0.97      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_692,c_3]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2283,plain,
% 2.37/0.97      ( k1_relat_1(sK3) = k1_xboole_0
% 2.37/0.97      | sK0 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_2141,c_753]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_2294,plain,
% 2.37/0.97      ( sK0 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(forward_subsumption_resolution,
% 2.37/0.97                [status(thm)],
% 2.37/0.97                [c_2282,c_2283]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_9,plain,
% 2.37/0.97      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.37/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.37/0.97      | k1_xboole_0 = X0 ),
% 2.37/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_223,plain,
% 2.37/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.37/0.97      | sK2 != k1_xboole_0
% 2.37/0.97      | sK0 != X0
% 2.37/0.97      | sK3 != k1_xboole_0
% 2.37/0.97      | k1_xboole_0 = X0 ),
% 2.37/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_98]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_224,plain,
% 2.37/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.37/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.37/0.97      | sK2 != k1_xboole_0
% 2.37/0.97      | sK3 != k1_xboole_0
% 2.37/0.97      | k1_xboole_0 = sK0 ),
% 2.37/0.97      inference(unflattening,[status(thm)],[c_223]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_695,plain,
% 2.37/0.97      ( sK2 != k1_xboole_0
% 2.37/0.97      | sK3 != k1_xboole_0
% 2.37/0.97      | k1_xboole_0 = sK0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.37/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_784,plain,
% 2.37/0.97      ( sK2 != k1_xboole_0
% 2.37/0.97      | sK0 = k1_xboole_0
% 2.37/0.97      | sK3 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.37/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_695,c_2]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1138,plain,
% 2.37/0.97      ( sK3 != k1_xboole_0
% 2.37/0.97      | sK0 = k1_xboole_0
% 2.37/0.97      | sK2 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(global_propositional_subsumption,
% 2.37/0.97                [status(thm)],
% 2.37/0.97                [c_784,c_18,c_23,c_841,c_941]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1139,plain,
% 2.37/0.97      ( sK2 != k1_xboole_0
% 2.37/0.97      | sK0 = k1_xboole_0
% 2.37/0.97      | sK3 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(renaming,[status(thm)],[c_1138]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1916,plain,
% 2.37/0.97      ( sK0 = k1_xboole_0
% 2.37/0.97      | sK3 != k1_xboole_0
% 2.37/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_1825,c_1139]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_856,plain,
% 2.37/0.97      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_859,plain,
% 2.37/0.97      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 2.37/0.97      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_459,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_944,plain,
% 2.37/0.97      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_459]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1178,plain,
% 2.37/0.97      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_944]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1179,plain,
% 2.37/0.97      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.37/0.97      inference(instantiation,[status(thm)],[c_1178]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1555,plain,
% 2.37/0.97      ( v1_xboole_0(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.37/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_1537,c_700]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1912,plain,
% 2.37/0.97      ( sK0 = k1_xboole_0
% 2.37/0.97      | v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) != iProver_top
% 2.37/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 2.37/0.97      inference(superposition,[status(thm)],[c_1825,c_1555]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1940,plain,
% 2.37/0.97      ( sK0 = k1_xboole_0
% 2.37/0.97      | v1_xboole_0(sK3) = iProver_top
% 2.37/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.37/0.97      inference(demodulation,[status(thm)],[c_1912,c_2]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(c_1953,plain,
% 2.37/0.97      ( sK0 = k1_xboole_0
% 2.37/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.37/0.97      inference(global_propositional_subsumption,
% 2.37/0.97                [status(thm)],
% 2.37/0.97                [c_1916,c_57,c_859,c_862,c_1139,c_1179,c_1825,c_1940]) ).
% 2.37/0.97  
% 2.37/0.97  cnf(contradiction,plain,
% 2.37/0.97      ( $false ),
% 2.37/0.97      inference(minisat,
% 2.37/0.97                [status(thm)],
% 2.37/0.97                [c_2716,c_2294,c_2132,c_1953,c_941,c_841,c_23,c_18]) ).
% 2.37/0.97  
% 2.37/0.97  
% 2.37/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.37/0.97  
% 2.37/0.97  ------                               Statistics
% 2.37/0.97  
% 2.37/0.97  ------ General
% 2.37/0.97  
% 2.37/0.97  abstr_ref_over_cycles:                  0
% 2.37/0.97  abstr_ref_under_cycles:                 0
% 2.37/0.97  gc_basic_clause_elim:                   0
% 2.37/0.97  forced_gc_time:                         0
% 2.37/0.97  parsing_time:                           0.017
% 2.37/0.97  unif_index_cands_time:                  0.
% 2.37/0.97  unif_index_add_time:                    0.
% 2.37/0.97  orderings_time:                         0.
% 2.37/0.97  out_proof_time:                         0.01
% 2.37/0.97  total_time:                             0.214
% 2.37/0.97  num_of_symbols:                         47
% 2.37/0.97  num_of_terms:                           2118
% 2.37/0.97  
% 2.37/0.97  ------ Preprocessing
% 2.37/0.97  
% 2.37/0.97  num_of_splits:                          0
% 2.37/0.97  num_of_split_atoms:                     0
% 2.37/0.97  num_of_reused_defs:                     0
% 2.37/0.97  num_eq_ax_congr_red:                    8
% 2.37/0.97  num_of_sem_filtered_clauses:            2
% 2.37/0.97  num_of_subtypes:                        0
% 2.37/0.97  monotx_restored_types:                  0
% 2.37/0.97  sat_num_of_epr_types:                   0
% 2.37/0.97  sat_num_of_non_cyclic_types:            0
% 2.37/0.97  sat_guarded_non_collapsed_types:        0
% 2.37/0.97  num_pure_diseq_elim:                    0
% 2.37/0.97  simp_replaced_by:                       0
% 2.37/0.97  res_preprocessed:                       92
% 2.37/0.97  prep_upred:                             0
% 2.37/0.97  prep_unflattend:                        34
% 2.37/0.97  smt_new_axioms:                         0
% 2.37/0.97  pred_elim_cands:                        2
% 2.37/0.97  pred_elim:                              2
% 2.37/0.97  pred_elim_cl:                           2
% 2.37/0.97  pred_elim_cycles:                       4
% 2.37/0.97  merged_defs:                            0
% 2.37/0.97  merged_defs_ncl:                        0
% 2.37/0.97  bin_hyper_res:                          0
% 2.37/0.97  prep_cycles:                            4
% 2.37/0.97  pred_elim_time:                         0.006
% 2.37/0.97  splitting_time:                         0.
% 2.37/0.97  sem_filter_time:                        0.
% 2.37/0.97  monotx_time:                            0.001
% 2.37/0.97  subtype_inf_time:                       0.
% 2.37/0.97  
% 2.37/0.97  ------ Problem properties
% 2.37/0.97  
% 2.37/0.97  clauses:                                18
% 2.37/0.97  conjectures:                            2
% 2.37/0.97  epr:                                    3
% 2.37/0.97  horn:                                   15
% 2.37/0.97  ground:                                 10
% 2.37/0.97  unary:                                  4
% 2.37/0.97  binary:                                 6
% 2.37/0.97  lits:                                   44
% 2.37/0.97  lits_eq:                                26
% 2.37/0.97  fd_pure:                                0
% 2.37/0.97  fd_pseudo:                              0
% 2.37/0.97  fd_cond:                                2
% 2.37/0.97  fd_pseudo_cond:                         0
% 2.37/0.97  ac_symbols:                             0
% 2.37/0.97  
% 2.37/0.97  ------ Propositional Solver
% 2.37/0.97  
% 2.37/0.97  prop_solver_calls:                      30
% 2.37/0.97  prop_fast_solver_calls:                 621
% 2.37/0.97  smt_solver_calls:                       0
% 2.37/0.97  smt_fast_solver_calls:                  0
% 2.37/0.97  prop_num_of_clauses:                    983
% 2.37/0.97  prop_preprocess_simplified:             3184
% 2.37/0.97  prop_fo_subsumed:                       14
% 2.37/0.97  prop_solver_time:                       0.
% 2.37/0.97  smt_solver_time:                        0.
% 2.37/0.97  smt_fast_solver_time:                   0.
% 2.37/0.97  prop_fast_solver_time:                  0.
% 2.37/0.97  prop_unsat_core_time:                   0.
% 2.37/0.97  
% 2.37/0.97  ------ QBF
% 2.37/0.97  
% 2.37/0.97  qbf_q_res:                              0
% 2.37/0.97  qbf_num_tautologies:                    0
% 2.37/0.97  qbf_prep_cycles:                        0
% 2.37/0.97  
% 2.37/0.97  ------ BMC1
% 2.37/0.97  
% 2.37/0.97  bmc1_current_bound:                     -1
% 2.37/0.97  bmc1_last_solved_bound:                 -1
% 2.37/0.97  bmc1_unsat_core_size:                   -1
% 2.37/0.97  bmc1_unsat_core_parents_size:           -1
% 2.37/0.97  bmc1_merge_next_fun:                    0
% 2.37/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.37/0.97  
% 2.37/0.97  ------ Instantiation
% 2.37/0.97  
% 2.37/0.97  inst_num_of_clauses:                    504
% 2.37/0.97  inst_num_in_passive:                    265
% 2.37/0.97  inst_num_in_active:                     226
% 2.37/0.97  inst_num_in_unprocessed:                13
% 2.37/0.97  inst_num_of_loops:                      270
% 2.37/0.97  inst_num_of_learning_restarts:          0
% 2.37/0.97  inst_num_moves_active_passive:          39
% 2.37/0.97  inst_lit_activity:                      0
% 2.37/0.97  inst_lit_activity_moves:                0
% 2.37/0.97  inst_num_tautologies:                   0
% 2.37/0.97  inst_num_prop_implied:                  0
% 2.37/0.97  inst_num_existing_simplified:           0
% 2.37/0.97  inst_num_eq_res_simplified:             0
% 2.37/0.97  inst_num_child_elim:                    0
% 2.37/0.97  inst_num_of_dismatching_blockings:      47
% 2.37/0.97  inst_num_of_non_proper_insts:           356
% 2.37/0.97  inst_num_of_duplicates:                 0
% 2.37/0.97  inst_inst_num_from_inst_to_res:         0
% 2.37/0.97  inst_dismatching_checking_time:         0.
% 2.37/0.97  
% 2.37/0.97  ------ Resolution
% 2.37/0.97  
% 2.37/0.97  res_num_of_clauses:                     0
% 2.37/0.97  res_num_in_passive:                     0
% 2.37/0.97  res_num_in_active:                      0
% 2.37/0.97  res_num_of_loops:                       96
% 2.37/0.97  res_forward_subset_subsumed:            26
% 2.37/0.97  res_backward_subset_subsumed:           0
% 2.37/0.97  res_forward_subsumed:                   0
% 2.37/0.97  res_backward_subsumed:                  0
% 2.37/0.97  res_forward_subsumption_resolution:     0
% 2.37/0.97  res_backward_subsumption_resolution:    0
% 2.37/0.97  res_clause_to_clause_subsumption:       126
% 2.37/0.97  res_orphan_elimination:                 0
% 2.37/0.97  res_tautology_del:                      71
% 2.37/0.97  res_num_eq_res_simplified:              1
% 2.37/0.97  res_num_sel_changes:                    0
% 2.37/0.97  res_moves_from_active_to_pass:          0
% 2.37/0.97  
% 2.37/0.97  ------ Superposition
% 2.37/0.97  
% 2.37/0.97  sup_time_total:                         0.
% 2.37/0.97  sup_time_generating:                    0.
% 2.37/0.97  sup_time_sim_full:                      0.
% 2.37/0.97  sup_time_sim_immed:                     0.
% 2.37/0.97  
% 2.37/0.97  sup_num_of_clauses:                     27
% 2.37/0.97  sup_num_in_active:                      17
% 2.37/0.97  sup_num_in_passive:                     10
% 2.37/0.97  sup_num_of_loops:                       53
% 2.37/0.97  sup_fw_superposition:                   18
% 2.37/0.97  sup_bw_superposition:                   33
% 2.37/0.97  sup_immediate_simplified:               15
% 2.37/0.97  sup_given_eliminated:                   0
% 2.37/0.97  comparisons_done:                       0
% 2.37/0.97  comparisons_avoided:                    15
% 2.37/0.97  
% 2.37/0.97  ------ Simplifications
% 2.37/0.97  
% 2.37/0.97  
% 2.37/0.97  sim_fw_subset_subsumed:                 9
% 2.37/0.97  sim_bw_subset_subsumed:                 3
% 2.37/0.97  sim_fw_subsumed:                        0
% 2.37/0.97  sim_bw_subsumed:                        8
% 2.37/0.97  sim_fw_subsumption_res:                 2
% 2.37/0.97  sim_bw_subsumption_res:                 2
% 2.37/0.97  sim_tautology_del:                      4
% 2.37/0.97  sim_eq_tautology_del:                   3
% 2.37/0.97  sim_eq_res_simp:                        1
% 2.37/0.97  sim_fw_demodulated:                     9
% 2.37/0.97  sim_bw_demodulated:                     34
% 2.37/0.97  sim_light_normalised:                   1
% 2.37/0.97  sim_joinable_taut:                      0
% 2.37/0.97  sim_joinable_simp:                      0
% 2.37/0.97  sim_ac_normalised:                      0
% 2.37/0.97  sim_smt_subsumption:                    0
% 2.37/0.97  
%------------------------------------------------------------------------------
