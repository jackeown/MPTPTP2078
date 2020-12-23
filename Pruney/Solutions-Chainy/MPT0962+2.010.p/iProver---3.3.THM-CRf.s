%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:10 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  152 (1687 expanded)
%              Number of clauses        :   95 ( 620 expanded)
%              Number of leaves         :   14 ( 293 expanded)
%              Depth                    :   22
%              Number of atoms          :  453 (6440 expanded)
%              Number of equality atoms :  237 (1912 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f31])).

fof(f58,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_979,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_127,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_24])).

cnf(c_128,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(renaming,[status(thm)],[c_127])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK1) != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_128])).

cnf(c_405,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_413,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_405,c_14])).

cnf(c_969,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_1471,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_969])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_602,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1130,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_1196,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_601,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1197,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK1),X1)
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1167,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_1225,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1226,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1478,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1471,c_25,c_23,c_413,c_1196,c_1197,c_1225,c_1226])).

cnf(c_974,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1484,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1478,c_974])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_299,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_295,c_12])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_1724,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_972])).

cnf(c_1747,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_1724])).

cnf(c_2132,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1747])).

cnf(c_74,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_76,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_2228,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2132,c_76])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_981,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2500,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2228,c_981])).

cnf(c_2690,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1484,c_2500])).

cnf(c_975,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_978,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2379,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_978])).

cnf(c_5152,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2379])).

cnf(c_980,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_975])).

cnf(c_2523,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_2377])).

cnf(c_5236,plain,
    ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5152,c_1724,c_2523])).

cnf(c_5237,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5236])).

cnf(c_5244,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_5237])).

cnf(c_26,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5628,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5244,c_26,c_76])).

cnf(c_2689,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_2500])).

cnf(c_5640,plain,
    ( k1_relat_1(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5628,c_2689])).

cnf(c_5506,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_2523])).

cnf(c_4991,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4992,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4991])).

cnf(c_4994,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4992])).

cnf(c_5667,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5506,c_26,c_76,c_4994,c_5244])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_976,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1806,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_976])).

cnf(c_5675,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_5667,c_1806])).

cnf(c_5691,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5640,c_5675])).

cnf(c_5715,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5691])).

cnf(c_5641,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5628,c_2500])).

cnf(c_16,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_361,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_relat_1(sK1) != X0
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_128])).

cnf(c_362,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_971,plain,
    ( sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_1049,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_971,c_3])).

cnf(c_69,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_1145,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_71,c_76])).

cnf(c_1146,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1145])).

cnf(c_1481,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1478,c_1146])).

cnf(c_1495,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1481])).

cnf(c_1499,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1495,c_3])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_128])).

cnf(c_389,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_970,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_1040,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_970,c_4])).

cnf(c_1482,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1478,c_1040])).

cnf(c_1491,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1482,c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5715,c_5641,c_5244,c_4994,c_1499,c_1491,c_76,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:32:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.85/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.05  
% 1.85/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.85/1.05  
% 1.85/1.05  ------  iProver source info
% 1.85/1.05  
% 1.85/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.85/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.85/1.05  git: non_committed_changes: false
% 1.85/1.05  git: last_make_outside_of_git: false
% 1.85/1.05  
% 1.85/1.05  ------ 
% 1.85/1.05  
% 1.85/1.05  ------ Input Options
% 1.85/1.05  
% 1.85/1.05  --out_options                           all
% 1.85/1.05  --tptp_safe_out                         true
% 1.85/1.05  --problem_path                          ""
% 1.85/1.05  --include_path                          ""
% 1.85/1.05  --clausifier                            res/vclausify_rel
% 1.85/1.05  --clausifier_options                    --mode clausify
% 1.85/1.05  --stdin                                 false
% 1.85/1.05  --stats_out                             all
% 1.85/1.05  
% 1.85/1.05  ------ General Options
% 1.85/1.05  
% 1.85/1.05  --fof                                   false
% 1.85/1.05  --time_out_real                         305.
% 1.85/1.05  --time_out_virtual                      -1.
% 1.85/1.05  --symbol_type_check                     false
% 1.85/1.05  --clausify_out                          false
% 1.85/1.05  --sig_cnt_out                           false
% 1.85/1.05  --trig_cnt_out                          false
% 1.85/1.05  --trig_cnt_out_tolerance                1.
% 1.85/1.05  --trig_cnt_out_sk_spl                   false
% 1.85/1.05  --abstr_cl_out                          false
% 1.85/1.05  
% 1.85/1.05  ------ Global Options
% 1.85/1.05  
% 1.85/1.05  --schedule                              default
% 1.85/1.05  --add_important_lit                     false
% 1.85/1.05  --prop_solver_per_cl                    1000
% 1.85/1.05  --min_unsat_core                        false
% 1.85/1.05  --soft_assumptions                      false
% 1.85/1.05  --soft_lemma_size                       3
% 1.85/1.05  --prop_impl_unit_size                   0
% 1.85/1.05  --prop_impl_unit                        []
% 1.85/1.05  --share_sel_clauses                     true
% 1.85/1.05  --reset_solvers                         false
% 1.85/1.05  --bc_imp_inh                            [conj_cone]
% 1.85/1.05  --conj_cone_tolerance                   3.
% 1.85/1.05  --extra_neg_conj                        none
% 1.85/1.05  --large_theory_mode                     true
% 1.85/1.05  --prolific_symb_bound                   200
% 1.85/1.05  --lt_threshold                          2000
% 1.85/1.05  --clause_weak_htbl                      true
% 1.85/1.05  --gc_record_bc_elim                     false
% 1.85/1.05  
% 1.85/1.05  ------ Preprocessing Options
% 1.85/1.05  
% 1.85/1.05  --preprocessing_flag                    true
% 1.85/1.05  --time_out_prep_mult                    0.1
% 1.85/1.05  --splitting_mode                        input
% 1.85/1.05  --splitting_grd                         true
% 1.85/1.05  --splitting_cvd                         false
% 1.85/1.05  --splitting_cvd_svl                     false
% 1.85/1.05  --splitting_nvd                         32
% 1.85/1.05  --sub_typing                            true
% 1.85/1.05  --prep_gs_sim                           true
% 1.85/1.05  --prep_unflatten                        true
% 1.85/1.05  --prep_res_sim                          true
% 1.85/1.05  --prep_upred                            true
% 1.85/1.05  --prep_sem_filter                       exhaustive
% 1.85/1.05  --prep_sem_filter_out                   false
% 1.85/1.05  --pred_elim                             true
% 1.85/1.05  --res_sim_input                         true
% 1.85/1.05  --eq_ax_congr_red                       true
% 1.85/1.05  --pure_diseq_elim                       true
% 1.85/1.05  --brand_transform                       false
% 1.85/1.05  --non_eq_to_eq                          false
% 1.85/1.05  --prep_def_merge                        true
% 1.85/1.05  --prep_def_merge_prop_impl              false
% 1.85/1.05  --prep_def_merge_mbd                    true
% 1.85/1.05  --prep_def_merge_tr_red                 false
% 1.85/1.05  --prep_def_merge_tr_cl                  false
% 1.85/1.05  --smt_preprocessing                     true
% 1.85/1.05  --smt_ac_axioms                         fast
% 1.85/1.05  --preprocessed_out                      false
% 1.85/1.05  --preprocessed_stats                    false
% 1.85/1.05  
% 1.85/1.05  ------ Abstraction refinement Options
% 1.85/1.05  
% 1.85/1.05  --abstr_ref                             []
% 1.85/1.05  --abstr_ref_prep                        false
% 1.85/1.05  --abstr_ref_until_sat                   false
% 1.85/1.05  --abstr_ref_sig_restrict                funpre
% 1.85/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.05  --abstr_ref_under                       []
% 1.85/1.05  
% 1.85/1.05  ------ SAT Options
% 1.85/1.05  
% 1.85/1.05  --sat_mode                              false
% 1.85/1.05  --sat_fm_restart_options                ""
% 1.85/1.05  --sat_gr_def                            false
% 1.85/1.05  --sat_epr_types                         true
% 1.85/1.05  --sat_non_cyclic_types                  false
% 1.85/1.05  --sat_finite_models                     false
% 1.85/1.05  --sat_fm_lemmas                         false
% 1.85/1.05  --sat_fm_prep                           false
% 1.85/1.05  --sat_fm_uc_incr                        true
% 1.85/1.05  --sat_out_model                         small
% 1.85/1.05  --sat_out_clauses                       false
% 1.85/1.05  
% 1.85/1.05  ------ QBF Options
% 1.85/1.05  
% 1.85/1.05  --qbf_mode                              false
% 1.85/1.05  --qbf_elim_univ                         false
% 1.85/1.05  --qbf_dom_inst                          none
% 1.85/1.05  --qbf_dom_pre_inst                      false
% 1.85/1.05  --qbf_sk_in                             false
% 1.85/1.05  --qbf_pred_elim                         true
% 1.85/1.05  --qbf_split                             512
% 1.85/1.05  
% 1.85/1.05  ------ BMC1 Options
% 1.85/1.05  
% 1.85/1.05  --bmc1_incremental                      false
% 1.85/1.05  --bmc1_axioms                           reachable_all
% 1.85/1.05  --bmc1_min_bound                        0
% 1.85/1.05  --bmc1_max_bound                        -1
% 1.85/1.05  --bmc1_max_bound_default                -1
% 1.85/1.05  --bmc1_symbol_reachability              true
% 1.85/1.05  --bmc1_property_lemmas                  false
% 1.85/1.05  --bmc1_k_induction                      false
% 1.85/1.05  --bmc1_non_equiv_states                 false
% 1.85/1.05  --bmc1_deadlock                         false
% 1.85/1.05  --bmc1_ucm                              false
% 1.85/1.05  --bmc1_add_unsat_core                   none
% 1.85/1.05  --bmc1_unsat_core_children              false
% 1.85/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.05  --bmc1_out_stat                         full
% 1.85/1.05  --bmc1_ground_init                      false
% 1.85/1.05  --bmc1_pre_inst_next_state              false
% 1.85/1.05  --bmc1_pre_inst_state                   false
% 1.85/1.05  --bmc1_pre_inst_reach_state             false
% 1.85/1.05  --bmc1_out_unsat_core                   false
% 1.85/1.05  --bmc1_aig_witness_out                  false
% 1.85/1.05  --bmc1_verbose                          false
% 1.85/1.05  --bmc1_dump_clauses_tptp                false
% 1.85/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.05  --bmc1_dump_file                        -
% 1.85/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.05  --bmc1_ucm_extend_mode                  1
% 1.85/1.05  --bmc1_ucm_init_mode                    2
% 1.85/1.05  --bmc1_ucm_cone_mode                    none
% 1.85/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.05  --bmc1_ucm_relax_model                  4
% 1.85/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.05  --bmc1_ucm_layered_model                none
% 1.85/1.05  --bmc1_ucm_max_lemma_size               10
% 1.85/1.05  
% 1.85/1.05  ------ AIG Options
% 1.85/1.05  
% 1.85/1.05  --aig_mode                              false
% 1.85/1.05  
% 1.85/1.05  ------ Instantiation Options
% 1.85/1.05  
% 1.85/1.05  --instantiation_flag                    true
% 1.85/1.05  --inst_sos_flag                         false
% 1.85/1.05  --inst_sos_phase                        true
% 1.85/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.05  --inst_lit_sel_side                     num_symb
% 1.85/1.05  --inst_solver_per_active                1400
% 1.85/1.05  --inst_solver_calls_frac                1.
% 1.85/1.05  --inst_passive_queue_type               priority_queues
% 1.85/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.05  --inst_passive_queues_freq              [25;2]
% 1.85/1.05  --inst_dismatching                      true
% 1.85/1.05  --inst_eager_unprocessed_to_passive     true
% 1.85/1.05  --inst_prop_sim_given                   true
% 1.85/1.05  --inst_prop_sim_new                     false
% 1.85/1.05  --inst_subs_new                         false
% 1.85/1.05  --inst_eq_res_simp                      false
% 1.85/1.05  --inst_subs_given                       false
% 1.85/1.05  --inst_orphan_elimination               true
% 1.85/1.05  --inst_learning_loop_flag               true
% 1.85/1.05  --inst_learning_start                   3000
% 1.85/1.05  --inst_learning_factor                  2
% 1.85/1.05  --inst_start_prop_sim_after_learn       3
% 1.85/1.05  --inst_sel_renew                        solver
% 1.85/1.05  --inst_lit_activity_flag                true
% 1.85/1.05  --inst_restr_to_given                   false
% 1.85/1.05  --inst_activity_threshold               500
% 1.85/1.05  --inst_out_proof                        true
% 1.85/1.05  
% 1.85/1.05  ------ Resolution Options
% 1.85/1.05  
% 1.85/1.05  --resolution_flag                       true
% 1.85/1.05  --res_lit_sel                           adaptive
% 1.85/1.05  --res_lit_sel_side                      none
% 1.85/1.05  --res_ordering                          kbo
% 1.85/1.05  --res_to_prop_solver                    active
% 1.85/1.05  --res_prop_simpl_new                    false
% 1.85/1.05  --res_prop_simpl_given                  true
% 1.85/1.05  --res_passive_queue_type                priority_queues
% 1.85/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.05  --res_passive_queues_freq               [15;5]
% 1.85/1.05  --res_forward_subs                      full
% 1.85/1.05  --res_backward_subs                     full
% 1.85/1.05  --res_forward_subs_resolution           true
% 1.85/1.05  --res_backward_subs_resolution          true
% 1.85/1.05  --res_orphan_elimination                true
% 1.85/1.05  --res_time_limit                        2.
% 1.85/1.05  --res_out_proof                         true
% 1.85/1.05  
% 1.85/1.05  ------ Superposition Options
% 1.85/1.05  
% 1.85/1.05  --superposition_flag                    true
% 1.85/1.05  --sup_passive_queue_type                priority_queues
% 1.85/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.05  --demod_completeness_check              fast
% 1.85/1.05  --demod_use_ground                      true
% 1.85/1.05  --sup_to_prop_solver                    passive
% 1.85/1.05  --sup_prop_simpl_new                    true
% 1.85/1.05  --sup_prop_simpl_given                  true
% 1.85/1.05  --sup_fun_splitting                     false
% 1.85/1.05  --sup_smt_interval                      50000
% 1.85/1.05  
% 1.85/1.05  ------ Superposition Simplification Setup
% 1.85/1.05  
% 1.85/1.05  --sup_indices_passive                   []
% 1.85/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.05  --sup_full_bw                           [BwDemod]
% 1.85/1.05  --sup_immed_triv                        [TrivRules]
% 1.85/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.05  --sup_immed_bw_main                     []
% 1.85/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.05  
% 1.85/1.05  ------ Combination Options
% 1.85/1.05  
% 1.85/1.05  --comb_res_mult                         3
% 1.85/1.05  --comb_sup_mult                         2
% 1.85/1.05  --comb_inst_mult                        10
% 1.85/1.05  
% 1.85/1.05  ------ Debug Options
% 1.85/1.05  
% 1.85/1.05  --dbg_backtrace                         false
% 1.85/1.05  --dbg_dump_prop_clauses                 false
% 1.85/1.05  --dbg_dump_prop_clauses_file            -
% 1.85/1.05  --dbg_out_stat                          false
% 1.85/1.05  ------ Parsing...
% 1.85/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.85/1.05  
% 1.85/1.05  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.85/1.05  
% 1.85/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.85/1.05  
% 1.85/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.85/1.05  ------ Proving...
% 1.85/1.05  ------ Problem Properties 
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  clauses                                 18
% 1.85/1.05  conjectures                             2
% 1.85/1.05  EPR                                     3
% 1.85/1.05  Horn                                    17
% 1.85/1.05  unary                                   7
% 1.85/1.05  binary                                  6
% 1.85/1.05  lits                                    38
% 1.85/1.05  lits eq                                 15
% 1.85/1.05  fd_pure                                 0
% 1.85/1.05  fd_pseudo                               0
% 1.85/1.05  fd_cond                                 1
% 1.85/1.05  fd_pseudo_cond                          1
% 1.85/1.05  AC symbols                              0
% 1.85/1.05  
% 1.85/1.05  ------ Schedule dynamic 5 is on 
% 1.85/1.05  
% 1.85/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  ------ 
% 1.85/1.05  Current options:
% 1.85/1.05  ------ 
% 1.85/1.05  
% 1.85/1.05  ------ Input Options
% 1.85/1.05  
% 1.85/1.05  --out_options                           all
% 1.85/1.05  --tptp_safe_out                         true
% 1.85/1.05  --problem_path                          ""
% 1.85/1.05  --include_path                          ""
% 1.85/1.05  --clausifier                            res/vclausify_rel
% 1.85/1.05  --clausifier_options                    --mode clausify
% 1.85/1.05  --stdin                                 false
% 1.85/1.05  --stats_out                             all
% 1.85/1.05  
% 1.85/1.05  ------ General Options
% 1.85/1.05  
% 1.85/1.05  --fof                                   false
% 1.85/1.05  --time_out_real                         305.
% 1.85/1.05  --time_out_virtual                      -1.
% 1.85/1.05  --symbol_type_check                     false
% 1.85/1.05  --clausify_out                          false
% 1.85/1.05  --sig_cnt_out                           false
% 1.85/1.05  --trig_cnt_out                          false
% 1.85/1.05  --trig_cnt_out_tolerance                1.
% 1.85/1.05  --trig_cnt_out_sk_spl                   false
% 1.85/1.05  --abstr_cl_out                          false
% 1.85/1.05  
% 1.85/1.05  ------ Global Options
% 1.85/1.05  
% 1.85/1.05  --schedule                              default
% 1.85/1.05  --add_important_lit                     false
% 1.85/1.05  --prop_solver_per_cl                    1000
% 1.85/1.05  --min_unsat_core                        false
% 1.85/1.05  --soft_assumptions                      false
% 1.85/1.05  --soft_lemma_size                       3
% 1.85/1.05  --prop_impl_unit_size                   0
% 1.85/1.05  --prop_impl_unit                        []
% 1.85/1.05  --share_sel_clauses                     true
% 1.85/1.05  --reset_solvers                         false
% 1.85/1.05  --bc_imp_inh                            [conj_cone]
% 1.85/1.05  --conj_cone_tolerance                   3.
% 1.85/1.05  --extra_neg_conj                        none
% 1.85/1.05  --large_theory_mode                     true
% 1.85/1.05  --prolific_symb_bound                   200
% 1.85/1.05  --lt_threshold                          2000
% 1.85/1.05  --clause_weak_htbl                      true
% 1.85/1.05  --gc_record_bc_elim                     false
% 1.85/1.05  
% 1.85/1.05  ------ Preprocessing Options
% 1.85/1.05  
% 1.85/1.05  --preprocessing_flag                    true
% 1.85/1.05  --time_out_prep_mult                    0.1
% 1.85/1.05  --splitting_mode                        input
% 1.85/1.05  --splitting_grd                         true
% 1.85/1.05  --splitting_cvd                         false
% 1.85/1.05  --splitting_cvd_svl                     false
% 1.85/1.05  --splitting_nvd                         32
% 1.85/1.05  --sub_typing                            true
% 1.85/1.05  --prep_gs_sim                           true
% 1.85/1.05  --prep_unflatten                        true
% 1.85/1.05  --prep_res_sim                          true
% 1.85/1.05  --prep_upred                            true
% 1.85/1.05  --prep_sem_filter                       exhaustive
% 1.85/1.05  --prep_sem_filter_out                   false
% 1.85/1.05  --pred_elim                             true
% 1.85/1.05  --res_sim_input                         true
% 1.85/1.05  --eq_ax_congr_red                       true
% 1.85/1.05  --pure_diseq_elim                       true
% 1.85/1.05  --brand_transform                       false
% 1.85/1.05  --non_eq_to_eq                          false
% 1.85/1.05  --prep_def_merge                        true
% 1.85/1.05  --prep_def_merge_prop_impl              false
% 1.85/1.05  --prep_def_merge_mbd                    true
% 1.85/1.05  --prep_def_merge_tr_red                 false
% 1.85/1.05  --prep_def_merge_tr_cl                  false
% 1.85/1.05  --smt_preprocessing                     true
% 1.85/1.05  --smt_ac_axioms                         fast
% 1.85/1.05  --preprocessed_out                      false
% 1.85/1.05  --preprocessed_stats                    false
% 1.85/1.05  
% 1.85/1.05  ------ Abstraction refinement Options
% 1.85/1.05  
% 1.85/1.05  --abstr_ref                             []
% 1.85/1.05  --abstr_ref_prep                        false
% 1.85/1.05  --abstr_ref_until_sat                   false
% 1.85/1.05  --abstr_ref_sig_restrict                funpre
% 1.85/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.05  --abstr_ref_under                       []
% 1.85/1.05  
% 1.85/1.05  ------ SAT Options
% 1.85/1.05  
% 1.85/1.05  --sat_mode                              false
% 1.85/1.05  --sat_fm_restart_options                ""
% 1.85/1.05  --sat_gr_def                            false
% 1.85/1.05  --sat_epr_types                         true
% 1.85/1.05  --sat_non_cyclic_types                  false
% 1.85/1.05  --sat_finite_models                     false
% 1.85/1.05  --sat_fm_lemmas                         false
% 1.85/1.05  --sat_fm_prep                           false
% 1.85/1.05  --sat_fm_uc_incr                        true
% 1.85/1.05  --sat_out_model                         small
% 1.85/1.05  --sat_out_clauses                       false
% 1.85/1.05  
% 1.85/1.05  ------ QBF Options
% 1.85/1.05  
% 1.85/1.05  --qbf_mode                              false
% 1.85/1.05  --qbf_elim_univ                         false
% 1.85/1.05  --qbf_dom_inst                          none
% 1.85/1.05  --qbf_dom_pre_inst                      false
% 1.85/1.05  --qbf_sk_in                             false
% 1.85/1.05  --qbf_pred_elim                         true
% 1.85/1.05  --qbf_split                             512
% 1.85/1.05  
% 1.85/1.05  ------ BMC1 Options
% 1.85/1.05  
% 1.85/1.05  --bmc1_incremental                      false
% 1.85/1.05  --bmc1_axioms                           reachable_all
% 1.85/1.05  --bmc1_min_bound                        0
% 1.85/1.05  --bmc1_max_bound                        -1
% 1.85/1.05  --bmc1_max_bound_default                -1
% 1.85/1.05  --bmc1_symbol_reachability              true
% 1.85/1.05  --bmc1_property_lemmas                  false
% 1.85/1.05  --bmc1_k_induction                      false
% 1.85/1.05  --bmc1_non_equiv_states                 false
% 1.85/1.05  --bmc1_deadlock                         false
% 1.85/1.05  --bmc1_ucm                              false
% 1.85/1.05  --bmc1_add_unsat_core                   none
% 1.85/1.05  --bmc1_unsat_core_children              false
% 1.85/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.05  --bmc1_out_stat                         full
% 1.85/1.05  --bmc1_ground_init                      false
% 1.85/1.05  --bmc1_pre_inst_next_state              false
% 1.85/1.05  --bmc1_pre_inst_state                   false
% 1.85/1.05  --bmc1_pre_inst_reach_state             false
% 1.85/1.05  --bmc1_out_unsat_core                   false
% 1.85/1.05  --bmc1_aig_witness_out                  false
% 1.85/1.05  --bmc1_verbose                          false
% 1.85/1.05  --bmc1_dump_clauses_tptp                false
% 1.85/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.05  --bmc1_dump_file                        -
% 1.85/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.05  --bmc1_ucm_extend_mode                  1
% 1.85/1.05  --bmc1_ucm_init_mode                    2
% 1.85/1.05  --bmc1_ucm_cone_mode                    none
% 1.85/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.05  --bmc1_ucm_relax_model                  4
% 1.85/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.05  --bmc1_ucm_layered_model                none
% 1.85/1.05  --bmc1_ucm_max_lemma_size               10
% 1.85/1.05  
% 1.85/1.05  ------ AIG Options
% 1.85/1.05  
% 1.85/1.05  --aig_mode                              false
% 1.85/1.05  
% 1.85/1.05  ------ Instantiation Options
% 1.85/1.05  
% 1.85/1.05  --instantiation_flag                    true
% 1.85/1.05  --inst_sos_flag                         false
% 1.85/1.05  --inst_sos_phase                        true
% 1.85/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.05  --inst_lit_sel_side                     none
% 1.85/1.05  --inst_solver_per_active                1400
% 1.85/1.05  --inst_solver_calls_frac                1.
% 1.85/1.05  --inst_passive_queue_type               priority_queues
% 1.85/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.05  --inst_passive_queues_freq              [25;2]
% 1.85/1.05  --inst_dismatching                      true
% 1.85/1.05  --inst_eager_unprocessed_to_passive     true
% 1.85/1.05  --inst_prop_sim_given                   true
% 1.85/1.05  --inst_prop_sim_new                     false
% 1.85/1.05  --inst_subs_new                         false
% 1.85/1.05  --inst_eq_res_simp                      false
% 1.85/1.05  --inst_subs_given                       false
% 1.85/1.05  --inst_orphan_elimination               true
% 1.85/1.05  --inst_learning_loop_flag               true
% 1.85/1.05  --inst_learning_start                   3000
% 1.85/1.05  --inst_learning_factor                  2
% 1.85/1.05  --inst_start_prop_sim_after_learn       3
% 1.85/1.05  --inst_sel_renew                        solver
% 1.85/1.05  --inst_lit_activity_flag                true
% 1.85/1.05  --inst_restr_to_given                   false
% 1.85/1.05  --inst_activity_threshold               500
% 1.85/1.05  --inst_out_proof                        true
% 1.85/1.05  
% 1.85/1.05  ------ Resolution Options
% 1.85/1.05  
% 1.85/1.05  --resolution_flag                       false
% 1.85/1.05  --res_lit_sel                           adaptive
% 1.85/1.05  --res_lit_sel_side                      none
% 1.85/1.05  --res_ordering                          kbo
% 1.85/1.05  --res_to_prop_solver                    active
% 1.85/1.05  --res_prop_simpl_new                    false
% 1.85/1.05  --res_prop_simpl_given                  true
% 1.85/1.05  --res_passive_queue_type                priority_queues
% 1.85/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.05  --res_passive_queues_freq               [15;5]
% 1.85/1.05  --res_forward_subs                      full
% 1.85/1.05  --res_backward_subs                     full
% 1.85/1.05  --res_forward_subs_resolution           true
% 1.85/1.05  --res_backward_subs_resolution          true
% 1.85/1.05  --res_orphan_elimination                true
% 1.85/1.05  --res_time_limit                        2.
% 1.85/1.05  --res_out_proof                         true
% 1.85/1.05  
% 1.85/1.05  ------ Superposition Options
% 1.85/1.05  
% 1.85/1.05  --superposition_flag                    true
% 1.85/1.05  --sup_passive_queue_type                priority_queues
% 1.85/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.05  --demod_completeness_check              fast
% 1.85/1.05  --demod_use_ground                      true
% 1.85/1.05  --sup_to_prop_solver                    passive
% 1.85/1.05  --sup_prop_simpl_new                    true
% 1.85/1.05  --sup_prop_simpl_given                  true
% 1.85/1.05  --sup_fun_splitting                     false
% 1.85/1.05  --sup_smt_interval                      50000
% 1.85/1.05  
% 1.85/1.05  ------ Superposition Simplification Setup
% 1.85/1.05  
% 1.85/1.05  --sup_indices_passive                   []
% 1.85/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.05  --sup_full_bw                           [BwDemod]
% 1.85/1.05  --sup_immed_triv                        [TrivRules]
% 1.85/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.05  --sup_immed_bw_main                     []
% 1.85/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.05  
% 1.85/1.05  ------ Combination Options
% 1.85/1.05  
% 1.85/1.05  --comb_res_mult                         3
% 1.85/1.05  --comb_sup_mult                         2
% 1.85/1.05  --comb_inst_mult                        10
% 1.85/1.05  
% 1.85/1.05  ------ Debug Options
% 1.85/1.05  
% 1.85/1.05  --dbg_backtrace                         false
% 1.85/1.05  --dbg_dump_prop_clauses                 false
% 1.85/1.05  --dbg_dump_prop_clauses_file            -
% 1.85/1.05  --dbg_out_stat                          false
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  ------ Proving...
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  % SZS status Theorem for theBenchmark.p
% 1.85/1.05  
% 1.85/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.85/1.05  
% 1.85/1.05  fof(f3,axiom,(
% 1.85/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f28,plain,(
% 1.85/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.85/1.05    inference(nnf_transformation,[],[f3])).
% 1.85/1.05  
% 1.85/1.05  fof(f40,plain,(
% 1.85/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.85/1.05    inference(cnf_transformation,[],[f28])).
% 1.85/1.05  
% 1.85/1.05  fof(f10,axiom,(
% 1.85/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f20,plain,(
% 1.85/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.05    inference(ennf_transformation,[],[f10])).
% 1.85/1.05  
% 1.85/1.05  fof(f21,plain,(
% 1.85/1.05    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.05    inference(flattening,[],[f20])).
% 1.85/1.05  
% 1.85/1.05  fof(f30,plain,(
% 1.85/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.05    inference(nnf_transformation,[],[f21])).
% 1.85/1.05  
% 1.85/1.05  fof(f51,plain,(
% 1.85/1.05    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.05    inference(cnf_transformation,[],[f30])).
% 1.85/1.05  
% 1.85/1.05  fof(f11,conjecture,(
% 1.85/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f12,negated_conjecture,(
% 1.85/1.05    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.85/1.05    inference(negated_conjecture,[],[f11])).
% 1.85/1.05  
% 1.85/1.05  fof(f22,plain,(
% 1.85/1.05    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.85/1.05    inference(ennf_transformation,[],[f12])).
% 1.85/1.05  
% 1.85/1.05  fof(f23,plain,(
% 1.85/1.05    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.85/1.05    inference(flattening,[],[f22])).
% 1.85/1.05  
% 1.85/1.05  fof(f31,plain,(
% 1.85/1.05    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.85/1.05    introduced(choice_axiom,[])).
% 1.85/1.05  
% 1.85/1.05  fof(f32,plain,(
% 1.85/1.05    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.85/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f31])).
% 1.85/1.05  
% 1.85/1.05  fof(f58,plain,(
% 1.85/1.05    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 1.85/1.05    inference(cnf_transformation,[],[f32])).
% 1.85/1.05  
% 1.85/1.05  fof(f56,plain,(
% 1.85/1.05    v1_funct_1(sK1)),
% 1.85/1.05    inference(cnf_transformation,[],[f32])).
% 1.85/1.05  
% 1.85/1.05  fof(f8,axiom,(
% 1.85/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f17,plain,(
% 1.85/1.05    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.05    inference(ennf_transformation,[],[f8])).
% 1.85/1.05  
% 1.85/1.05  fof(f47,plain,(
% 1.85/1.05    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.05    inference(cnf_transformation,[],[f17])).
% 1.85/1.05  
% 1.85/1.05  fof(f55,plain,(
% 1.85/1.05    v1_relat_1(sK1)),
% 1.85/1.05    inference(cnf_transformation,[],[f32])).
% 1.85/1.05  
% 1.85/1.05  fof(f57,plain,(
% 1.85/1.05    r1_tarski(k2_relat_1(sK1),sK0)),
% 1.85/1.05    inference(cnf_transformation,[],[f32])).
% 1.85/1.05  
% 1.85/1.05  fof(f9,axiom,(
% 1.85/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f18,plain,(
% 1.85/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.85/1.05    inference(ennf_transformation,[],[f9])).
% 1.85/1.05  
% 1.85/1.05  fof(f19,plain,(
% 1.85/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.85/1.05    inference(flattening,[],[f18])).
% 1.85/1.05  
% 1.85/1.05  fof(f48,plain,(
% 1.85/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.85/1.05    inference(cnf_transformation,[],[f19])).
% 1.85/1.05  
% 1.85/1.05  fof(f1,axiom,(
% 1.85/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f24,plain,(
% 1.85/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/1.05    inference(nnf_transformation,[],[f1])).
% 1.85/1.05  
% 1.85/1.05  fof(f25,plain,(
% 1.85/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/1.05    inference(flattening,[],[f24])).
% 1.85/1.05  
% 1.85/1.05  fof(f33,plain,(
% 1.85/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.85/1.05    inference(cnf_transformation,[],[f25])).
% 1.85/1.05  
% 1.85/1.05  fof(f60,plain,(
% 1.85/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.85/1.05    inference(equality_resolution,[],[f33])).
% 1.85/1.05  
% 1.85/1.05  fof(f5,axiom,(
% 1.85/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f43,plain,(
% 1.85/1.05    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.85/1.05    inference(cnf_transformation,[],[f5])).
% 1.85/1.05  
% 1.85/1.05  fof(f2,axiom,(
% 1.85/1.05    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f26,plain,(
% 1.85/1.05    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.85/1.05    inference(nnf_transformation,[],[f2])).
% 1.85/1.05  
% 1.85/1.05  fof(f27,plain,(
% 1.85/1.05    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.85/1.05    inference(flattening,[],[f26])).
% 1.85/1.05  
% 1.85/1.05  fof(f38,plain,(
% 1.85/1.05    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.85/1.05    inference(cnf_transformation,[],[f27])).
% 1.85/1.05  
% 1.85/1.05  fof(f61,plain,(
% 1.85/1.05    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.85/1.05    inference(equality_resolution,[],[f38])).
% 1.85/1.05  
% 1.85/1.05  fof(f7,axiom,(
% 1.85/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f13,plain,(
% 1.85/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.85/1.05    inference(pure_predicate_removal,[],[f7])).
% 1.85/1.05  
% 1.85/1.05  fof(f16,plain,(
% 1.85/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.05    inference(ennf_transformation,[],[f13])).
% 1.85/1.05  
% 1.85/1.05  fof(f46,plain,(
% 1.85/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.05    inference(cnf_transformation,[],[f16])).
% 1.85/1.05  
% 1.85/1.05  fof(f4,axiom,(
% 1.85/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f14,plain,(
% 1.85/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.85/1.05    inference(ennf_transformation,[],[f4])).
% 1.85/1.05  
% 1.85/1.05  fof(f29,plain,(
% 1.85/1.05    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.85/1.05    inference(nnf_transformation,[],[f14])).
% 1.85/1.05  
% 1.85/1.05  fof(f41,plain,(
% 1.85/1.05    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.85/1.05    inference(cnf_transformation,[],[f29])).
% 1.85/1.05  
% 1.85/1.05  fof(f6,axiom,(
% 1.85/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.85/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.85/1.05  
% 1.85/1.05  fof(f15,plain,(
% 1.85/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/1.05    inference(ennf_transformation,[],[f6])).
% 1.85/1.05  
% 1.85/1.05  fof(f45,plain,(
% 1.85/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.05    inference(cnf_transformation,[],[f15])).
% 1.85/1.05  
% 1.85/1.05  fof(f35,plain,(
% 1.85/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.85/1.05    inference(cnf_transformation,[],[f25])).
% 1.85/1.05  
% 1.85/1.05  fof(f39,plain,(
% 1.85/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.85/1.05    inference(cnf_transformation,[],[f28])).
% 1.85/1.05  
% 1.85/1.05  fof(f37,plain,(
% 1.85/1.05    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.85/1.05    inference(cnf_transformation,[],[f27])).
% 1.85/1.05  
% 1.85/1.05  fof(f62,plain,(
% 1.85/1.05    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 1.85/1.05    inference(equality_resolution,[],[f37])).
% 1.85/1.05  
% 1.85/1.05  fof(f54,plain,(
% 1.85/1.05    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.05    inference(cnf_transformation,[],[f30])).
% 1.85/1.05  
% 1.85/1.05  fof(f63,plain,(
% 1.85/1.05    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.05    inference(equality_resolution,[],[f54])).
% 1.85/1.05  
% 1.85/1.05  fof(f64,plain,(
% 1.85/1.05    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.85/1.05    inference(equality_resolution,[],[f63])).
% 1.85/1.05  
% 1.85/1.05  fof(f52,plain,(
% 1.85/1.05    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/1.05    inference(cnf_transformation,[],[f30])).
% 1.85/1.05  
% 1.85/1.05  fof(f66,plain,(
% 1.85/1.05    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.85/1.05    inference(equality_resolution,[],[f52])).
% 1.85/1.05  
% 1.85/1.05  cnf(c_6,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.85/1.05      inference(cnf_transformation,[],[f40]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_979,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.85/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_19,plain,
% 1.85/1.05      ( v1_funct_2(X0,X1,X2)
% 1.85/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.05      | k1_relset_1(X1,X2,X0) != X1
% 1.85/1.05      | k1_xboole_0 = X2 ),
% 1.85/1.05      inference(cnf_transformation,[],[f51]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_22,negated_conjecture,
% 1.85/1.05      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 1.85/1.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | ~ v1_funct_1(sK1) ),
% 1.85/1.05      inference(cnf_transformation,[],[f58]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_24,negated_conjecture,
% 1.85/1.05      ( v1_funct_1(sK1) ),
% 1.85/1.05      inference(cnf_transformation,[],[f56]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_127,plain,
% 1.85/1.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_22,c_24]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_128,negated_conjecture,
% 1.85/1.05      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 1.85/1.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
% 1.85/1.05      inference(renaming,[status(thm)],[c_127]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_404,plain,
% 1.85/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | k1_relset_1(X1,X2,X0) != X1
% 1.85/1.05      | k1_relat_1(sK1) != X1
% 1.85/1.05      | sK0 != X2
% 1.85/1.05      | sK1 != X0
% 1.85/1.05      | k1_xboole_0 = X2 ),
% 1.85/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_128]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_405,plain,
% 1.85/1.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
% 1.85/1.05      | k1_xboole_0 = sK0 ),
% 1.85/1.05      inference(unflattening,[status(thm)],[c_404]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_14,plain,
% 1.85/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.85/1.05      inference(cnf_transformation,[],[f47]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_413,plain,
% 1.85/1.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | k1_xboole_0 = sK0 ),
% 1.85/1.05      inference(forward_subsumption_resolution,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_405,c_14]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_969,plain,
% 1.85/1.05      ( k1_xboole_0 = sK0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1471,plain,
% 1.85/1.05      ( sK0 = k1_xboole_0
% 1.85/1.05      | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_979,c_969]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_25,negated_conjecture,
% 1.85/1.05      ( v1_relat_1(sK1) ),
% 1.85/1.05      inference(cnf_transformation,[],[f55]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_23,negated_conjecture,
% 1.85/1.05      ( r1_tarski(k2_relat_1(sK1),sK0) ),
% 1.85/1.05      inference(cnf_transformation,[],[f57]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_602,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1130,plain,
% 1.85/1.05      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_602]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1196,plain,
% 1.85/1.05      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_1130]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_601,plain,( X0 = X0 ),theory(equality) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1197,plain,
% 1.85/1.05      ( sK0 = sK0 ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_601]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_15,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.05      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.85/1.05      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.85/1.05      | ~ v1_relat_1(X0) ),
% 1.85/1.05      inference(cnf_transformation,[],[f48]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1122,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.85/1.05      | ~ r1_tarski(k2_relat_1(sK1),X1)
% 1.85/1.05      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 1.85/1.05      | ~ v1_relat_1(sK1) ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_15]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1167,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 1.85/1.05      | ~ r1_tarski(k2_relat_1(sK1),sK0)
% 1.85/1.05      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 1.85/1.05      | ~ v1_relat_1(sK1) ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_1122]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1225,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | ~ r1_tarski(k2_relat_1(sK1),sK0)
% 1.85/1.05      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 1.85/1.05      | ~ v1_relat_1(sK1) ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_1167]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2,plain,
% 1.85/1.05      ( r1_tarski(X0,X0) ),
% 1.85/1.05      inference(cnf_transformation,[],[f60]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1226,plain,
% 1.85/1.05      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_2]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1478,plain,
% 1.85/1.05      ( sK0 = k1_xboole_0 ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_1471,c_25,c_23,c_413,c_1196,c_1197,c_1225,c_1226]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_974,plain,
% 1.85/1.05      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1484,plain,
% 1.85/1.05      ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_1478,c_974]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_11,plain,
% 1.85/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.85/1.05      inference(cnf_transformation,[],[f43]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_3,plain,
% 1.85/1.05      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.85/1.05      inference(cnf_transformation,[],[f61]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_13,plain,
% 1.85/1.05      ( v4_relat_1(X0,X1)
% 1.85/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.85/1.05      inference(cnf_transformation,[],[f46]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_9,plain,
% 1.85/1.05      ( ~ v4_relat_1(X0,X1)
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1)
% 1.85/1.05      | ~ v1_relat_1(X0) ),
% 1.85/1.05      inference(cnf_transformation,[],[f41]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_295,plain,
% 1.85/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1)
% 1.85/1.05      | ~ v1_relat_1(X0) ),
% 1.85/1.05      inference(resolution,[status(thm)],[c_13,c_9]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_12,plain,
% 1.85/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.05      | v1_relat_1(X0) ),
% 1.85/1.05      inference(cnf_transformation,[],[f45]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_299,plain,
% 1.85/1.05      ( r1_tarski(k1_relat_1(X0),X1)
% 1.85/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_295,c_12]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_300,plain,
% 1.85/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.85/1.05      inference(renaming,[status(thm)],[c_299]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_972,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1724,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_3,c_972]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1747,plain,
% 1.85/1.05      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_979,c_1724]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2132,plain,
% 1.85/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 1.85/1.05      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_11,c_1747]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_74,plain,
% 1.85/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_76,plain,
% 1.85/1.05      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_74]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2228,plain,
% 1.85/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_2132,c_76]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_0,plain,
% 1.85/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.85/1.05      inference(cnf_transformation,[],[f35]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_981,plain,
% 1.85/1.05      ( X0 = X1
% 1.85/1.05      | r1_tarski(X0,X1) != iProver_top
% 1.85/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2500,plain,
% 1.85/1.05      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_2228,c_981]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2690,plain,
% 1.85/1.05      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_1484,c_2500]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_975,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 1.85/1.05      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 1.85/1.05      | v1_relat_1(X0) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_7,plain,
% 1.85/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.85/1.05      inference(cnf_transformation,[],[f39]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_978,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.85/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2379,plain,
% 1.85/1.05      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 1.85/1.05      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 1.85/1.05      | v1_relat_1(X0) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_975,c_978]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5152,plain,
% 1.85/1.05      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 1.85/1.05      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 1.85/1.05      | v1_relat_1(X0) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_3,c_2379]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_980,plain,
% 1.85/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2377,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.85/1.05      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 1.85/1.05      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 1.85/1.05      | v1_relat_1(X0) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_3,c_975]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2523,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.85/1.05      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 1.85/1.05      | v1_relat_1(X0) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_980,c_2377]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5236,plain,
% 1.85/1.05      ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 1.85/1.05      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 1.85/1.05      | v1_relat_1(X0) != iProver_top ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_5152,c_1724,c_2523]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5237,plain,
% 1.85/1.05      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 1.85/1.05      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 1.85/1.05      | v1_relat_1(X0) != iProver_top ),
% 1.85/1.05      inference(renaming,[status(thm)],[c_5236]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5244,plain,
% 1.85/1.05      ( r1_tarski(sK1,k1_xboole_0) = iProver_top
% 1.85/1.05      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 1.85/1.05      | v1_relat_1(sK1) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_2690,c_5237]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_26,plain,
% 1.85/1.05      ( v1_relat_1(sK1) = iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5628,plain,
% 1.85/1.05      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_5244,c_26,c_76]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_2689,plain,
% 1.85/1.05      ( k1_relat_1(X0) = k1_xboole_0
% 1.85/1.05      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_1747,c_2500]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5640,plain,
% 1.85/1.05      ( k1_relat_1(sK1) = k1_xboole_0 ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_5628,c_2689]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5506,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.85/1.05      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 1.85/1.05      | v1_relat_1(sK1) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_2690,c_2523]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_4991,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~ r1_tarski(sK1,X0) ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_4992,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(X0)) = iProver_top
% 1.85/1.05      | r1_tarski(sK1,X0) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_4991]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_4994,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.85/1.05      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_4992]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5667,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_5506,c_26,c_76,c_4994,c_5244]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_4,plain,
% 1.85/1.05      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.85/1.05      inference(cnf_transformation,[],[f62]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_976,plain,
% 1.85/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.85/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1806,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 1.85/1.05      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_4,c_976]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5675,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_relat_1(sK1) ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_5667,c_1806]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5691,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_xboole_0 ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_5640,c_5675]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5715,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_5691]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_5641,plain,
% 1.85/1.05      ( sK1 = k1_xboole_0 ),
% 1.85/1.05      inference(superposition,[status(thm)],[c_5628,c_2500]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_16,plain,
% 1.85/1.05      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 1.85/1.05      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 1.85/1.05      | k1_xboole_0 = X0 ),
% 1.85/1.05      inference(cnf_transformation,[],[f64]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_361,plain,
% 1.85/1.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 1.85/1.05      | k1_relat_1(sK1) != X0
% 1.85/1.05      | sK0 != k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | k1_xboole_0 = X0 ),
% 1.85/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_128]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_362,plain,
% 1.85/1.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
% 1.85/1.05      | sK0 != k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | k1_xboole_0 = k1_relat_1(sK1) ),
% 1.85/1.05      inference(unflattening,[status(thm)],[c_361]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_971,plain,
% 1.85/1.05      ( sK0 != k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | k1_xboole_0 = k1_relat_1(sK1)
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 1.85/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1049,plain,
% 1.85/1.05      ( k1_relat_1(sK1) = k1_xboole_0
% 1.85/1.05      | sK0 != k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 1.85/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_971,c_3]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_69,plain,
% 1.85/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.85/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_71,plain,
% 1.85/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.85/1.05      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.85/1.05      inference(instantiation,[status(thm)],[c_69]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1145,plain,
% 1.85/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | sK0 != k1_xboole_0
% 1.85/1.05      | k1_relat_1(sK1) = k1_xboole_0 ),
% 1.85/1.05      inference(global_propositional_subsumption,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_1049,c_71,c_76]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1146,plain,
% 1.85/1.05      ( k1_relat_1(sK1) = k1_xboole_0
% 1.85/1.05      | sK0 != k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 1.85/1.05      inference(renaming,[status(thm)],[c_1145]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1481,plain,
% 1.85/1.05      ( k1_relat_1(sK1) = k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | k1_xboole_0 != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_1478,c_1146]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1495,plain,
% 1.85/1.05      ( k1_relat_1(sK1) = k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
% 1.85/1.05      inference(equality_resolution_simp,[status(thm)],[c_1481]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1499,plain,
% 1.85/1.05      ( k1_relat_1(sK1) = k1_xboole_0
% 1.85/1.05      | sK1 != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_1495,c_3]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_18,plain,
% 1.85/1.05      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.85/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.85/1.05      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.85/1.05      inference(cnf_transformation,[],[f66]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_388,plain,
% 1.85/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.85/1.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.85/1.05      | k1_relat_1(sK1) != k1_xboole_0
% 1.85/1.05      | sK0 != X1
% 1.85/1.05      | sK1 != X0 ),
% 1.85/1.05      inference(resolution_lifted,[status(thm)],[c_18,c_128]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_389,plain,
% 1.85/1.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.85/1.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.85/1.05      | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 1.85/1.05      | k1_relat_1(sK1) != k1_xboole_0 ),
% 1.85/1.05      inference(unflattening,[status(thm)],[c_388]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_970,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 1.85/1.05      | k1_relat_1(sK1) != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.85/1.05      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1040,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 1.85/1.05      | k1_relat_1(sK1) != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_970,c_4]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1482,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.85/1.05      | k1_relat_1(sK1) != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_1478,c_1040]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(c_1491,plain,
% 1.85/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.85/1.05      | k1_relat_1(sK1) != k1_xboole_0
% 1.85/1.05      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.85/1.05      inference(demodulation,[status(thm)],[c_1482,c_3]) ).
% 1.85/1.05  
% 1.85/1.05  cnf(contradiction,plain,
% 1.85/1.05      ( $false ),
% 1.85/1.05      inference(minisat,
% 1.85/1.05                [status(thm)],
% 1.85/1.05                [c_5715,c_5641,c_5244,c_4994,c_1499,c_1491,c_76,c_26]) ).
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.85/1.05  
% 1.85/1.05  ------                               Statistics
% 1.85/1.05  
% 1.85/1.05  ------ General
% 1.85/1.05  
% 1.85/1.05  abstr_ref_over_cycles:                  0
% 1.85/1.05  abstr_ref_under_cycles:                 0
% 1.85/1.05  gc_basic_clause_elim:                   0
% 1.85/1.05  forced_gc_time:                         0
% 1.85/1.05  parsing_time:                           0.011
% 1.85/1.05  unif_index_cands_time:                  0.
% 1.85/1.05  unif_index_add_time:                    0.
% 1.85/1.05  orderings_time:                         0.
% 1.85/1.05  out_proof_time:                         0.009
% 1.85/1.05  total_time:                             0.187
% 1.85/1.05  num_of_symbols:                         45
% 1.85/1.05  num_of_terms:                           4342
% 1.85/1.05  
% 1.85/1.05  ------ Preprocessing
% 1.85/1.05  
% 1.85/1.05  num_of_splits:                          0
% 1.85/1.05  num_of_split_atoms:                     0
% 1.85/1.05  num_of_reused_defs:                     0
% 1.85/1.05  num_eq_ax_congr_red:                    4
% 1.85/1.05  num_of_sem_filtered_clauses:            2
% 1.85/1.05  num_of_subtypes:                        0
% 1.85/1.05  monotx_restored_types:                  0
% 1.85/1.05  sat_num_of_epr_types:                   0
% 1.85/1.05  sat_num_of_non_cyclic_types:            0
% 1.85/1.05  sat_guarded_non_collapsed_types:        0
% 1.85/1.05  num_pure_diseq_elim:                    0
% 1.85/1.05  simp_replaced_by:                       0
% 1.85/1.05  res_preprocessed:                       100
% 1.85/1.05  prep_upred:                             0
% 1.85/1.05  prep_unflattend:                        28
% 1.85/1.05  smt_new_axioms:                         0
% 1.85/1.05  pred_elim_cands:                        3
% 1.85/1.05  pred_elim:                              2
% 1.85/1.05  pred_elim_cl:                           6
% 1.85/1.05  pred_elim_cycles:                       5
% 1.85/1.05  merged_defs:                            8
% 1.85/1.05  merged_defs_ncl:                        0
% 1.85/1.05  bin_hyper_res:                          8
% 1.85/1.05  prep_cycles:                            4
% 1.85/1.05  pred_elim_time:                         0.006
% 1.85/1.05  splitting_time:                         0.
% 1.85/1.05  sem_filter_time:                        0.
% 1.85/1.05  monotx_time:                            0.001
% 1.85/1.05  subtype_inf_time:                       0.
% 1.85/1.05  
% 1.85/1.05  ------ Problem properties
% 1.85/1.05  
% 1.85/1.05  clauses:                                18
% 1.85/1.05  conjectures:                            2
% 1.85/1.05  epr:                                    3
% 1.85/1.05  horn:                                   17
% 1.85/1.05  ground:                                 7
% 1.85/1.05  unary:                                  7
% 1.85/1.05  binary:                                 6
% 1.85/1.05  lits:                                   38
% 1.85/1.05  lits_eq:                                15
% 1.85/1.05  fd_pure:                                0
% 1.85/1.05  fd_pseudo:                              0
% 1.85/1.05  fd_cond:                                1
% 1.85/1.05  fd_pseudo_cond:                         1
% 1.85/1.05  ac_symbols:                             0
% 1.85/1.05  
% 1.85/1.05  ------ Propositional Solver
% 1.85/1.05  
% 1.85/1.05  prop_solver_calls:                      30
% 1.85/1.05  prop_fast_solver_calls:                 666
% 1.85/1.05  smt_solver_calls:                       0
% 1.85/1.05  smt_fast_solver_calls:                  0
% 1.85/1.05  prop_num_of_clauses:                    1888
% 1.85/1.05  prop_preprocess_simplified:             4832
% 1.85/1.05  prop_fo_subsumed:                       12
% 1.85/1.05  prop_solver_time:                       0.
% 1.85/1.05  smt_solver_time:                        0.
% 1.85/1.05  smt_fast_solver_time:                   0.
% 1.85/1.05  prop_fast_solver_time:                  0.
% 1.85/1.05  prop_unsat_core_time:                   0.
% 1.85/1.05  
% 1.85/1.05  ------ QBF
% 1.85/1.05  
% 1.85/1.05  qbf_q_res:                              0
% 1.85/1.05  qbf_num_tautologies:                    0
% 1.85/1.05  qbf_prep_cycles:                        0
% 1.85/1.05  
% 1.85/1.05  ------ BMC1
% 1.85/1.05  
% 1.85/1.05  bmc1_current_bound:                     -1
% 1.85/1.05  bmc1_last_solved_bound:                 -1
% 1.85/1.05  bmc1_unsat_core_size:                   -1
% 1.85/1.05  bmc1_unsat_core_parents_size:           -1
% 1.85/1.05  bmc1_merge_next_fun:                    0
% 1.85/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.85/1.05  
% 1.85/1.05  ------ Instantiation
% 1.85/1.05  
% 1.85/1.05  inst_num_of_clauses:                    575
% 1.85/1.05  inst_num_in_passive:                    161
% 1.85/1.05  inst_num_in_active:                     339
% 1.85/1.05  inst_num_in_unprocessed:                76
% 1.85/1.05  inst_num_of_loops:                      390
% 1.85/1.05  inst_num_of_learning_restarts:          0
% 1.85/1.05  inst_num_moves_active_passive:          47
% 1.85/1.05  inst_lit_activity:                      0
% 1.85/1.05  inst_lit_activity_moves:                0
% 1.85/1.05  inst_num_tautologies:                   0
% 1.85/1.05  inst_num_prop_implied:                  0
% 1.85/1.05  inst_num_existing_simplified:           0
% 1.85/1.05  inst_num_eq_res_simplified:             0
% 1.85/1.05  inst_num_child_elim:                    0
% 1.85/1.05  inst_num_of_dismatching_blockings:      192
% 1.85/1.05  inst_num_of_non_proper_insts:           890
% 1.85/1.05  inst_num_of_duplicates:                 0
% 1.85/1.05  inst_inst_num_from_inst_to_res:         0
% 1.85/1.05  inst_dismatching_checking_time:         0.
% 1.85/1.05  
% 1.85/1.05  ------ Resolution
% 1.85/1.05  
% 1.85/1.05  res_num_of_clauses:                     0
% 1.85/1.05  res_num_in_passive:                     0
% 1.85/1.05  res_num_in_active:                      0
% 1.85/1.05  res_num_of_loops:                       104
% 1.85/1.05  res_forward_subset_subsumed:            54
% 1.85/1.05  res_backward_subset_subsumed:           2
% 1.85/1.05  res_forward_subsumed:                   0
% 1.85/1.05  res_backward_subsumed:                  0
% 1.85/1.05  res_forward_subsumption_resolution:     1
% 1.85/1.05  res_backward_subsumption_resolution:    0
% 1.85/1.05  res_clause_to_clause_subsumption:       614
% 1.85/1.05  res_orphan_elimination:                 0
% 1.85/1.05  res_tautology_del:                      77
% 1.85/1.05  res_num_eq_res_simplified:              0
% 1.85/1.05  res_num_sel_changes:                    0
% 1.85/1.05  res_moves_from_active_to_pass:          0
% 1.85/1.05  
% 1.85/1.05  ------ Superposition
% 1.85/1.05  
% 1.85/1.05  sup_time_total:                         0.
% 1.85/1.05  sup_time_generating:                    0.
% 1.85/1.05  sup_time_sim_full:                      0.
% 1.85/1.05  sup_time_sim_immed:                     0.
% 1.85/1.05  
% 1.85/1.05  sup_num_of_clauses:                     99
% 1.85/1.05  sup_num_in_active:                      65
% 1.85/1.05  sup_num_in_passive:                     34
% 1.85/1.05  sup_num_of_loops:                       77
% 1.85/1.05  sup_fw_superposition:                   184
% 1.85/1.05  sup_bw_superposition:                   96
% 1.85/1.05  sup_immediate_simplified:               121
% 1.85/1.05  sup_given_eliminated:                   4
% 1.85/1.05  comparisons_done:                       0
% 1.85/1.05  comparisons_avoided:                    0
% 1.85/1.05  
% 1.85/1.05  ------ Simplifications
% 1.85/1.05  
% 1.85/1.05  
% 1.85/1.05  sim_fw_subset_subsumed:                 1
% 1.85/1.05  sim_bw_subset_subsumed:                 3
% 1.85/1.05  sim_fw_subsumed:                        28
% 1.85/1.05  sim_bw_subsumed:                        9
% 1.85/1.05  sim_fw_subsumption_res:                 0
% 1.85/1.05  sim_bw_subsumption_res:                 0
% 1.85/1.05  sim_tautology_del:                      9
% 1.85/1.05  sim_eq_tautology_del:                   53
% 1.85/1.05  sim_eq_res_simp:                        1
% 1.85/1.05  sim_fw_demodulated:                     35
% 1.85/1.05  sim_bw_demodulated:                     17
% 1.85/1.05  sim_light_normalised:                   83
% 1.85/1.05  sim_joinable_taut:                      0
% 1.85/1.05  sim_joinable_simp:                      0
% 1.85/1.05  sim_ac_normalised:                      0
% 1.85/1.05  sim_smt_subsumption:                    0
% 1.85/1.05  
%------------------------------------------------------------------------------
