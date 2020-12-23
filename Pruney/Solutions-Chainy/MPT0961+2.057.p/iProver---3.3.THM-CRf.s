%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:05 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 793 expanded)
%              Number of clauses        :   82 ( 296 expanded)
%              Number of leaves         :   17 ( 158 expanded)
%              Depth                    :   22
%              Number of atoms          :  374 (2579 expanded)
%              Number of equality atoms :  220 ( 780 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
        | ~ v1_funct_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
      | ~ v1_funct_1(sK1) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f33])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f38])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f39])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_719,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_720,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1549,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_720])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_278,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_279,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ r1_tarski(k2_relat_1(sK1),X1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_714,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_22])).

cnf(c_117,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    inference(renaming,[status(thm)],[c_116])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK1) != X1
    | k2_relat_1(sK1) != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_117])).

cnf(c_377,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_385,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_377,c_13])).

cnf(c_711,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_855,plain,
    ( k2_relat_1(sK1) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_711])).

cnf(c_1729,plain,
    ( k2_relat_1(sK1) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_855])).

cnf(c_1732,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1729,c_1549])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | k2_relat_1(sK1) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_117])).

cnf(c_361,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_712,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_788,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_712,c_3])).

cnf(c_2053,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1732,c_788])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2068,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2053,c_2])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_69,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_70,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_301,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_302,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_499,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_857,plain,
    ( k1_relat_1(sK1) != X0
    | k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_902,plain,
    ( k1_relat_1(sK1) != k1_relat_1(X0)
    | k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_904,plain,
    ( k1_relat_1(sK1) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_505,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_903,plain,
    ( k1_relat_1(sK1) = k1_relat_1(X0)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_905,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_859,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_913,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_498,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_914,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_500,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_926,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK1),X1)
    | k2_relat_1(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_927,plain,
    ( k2_relat_1(sK1) != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_929,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_1032,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_1033,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_269,plain,
    ( k6_relat_1(X0) != X1
    | k2_relat_1(X1) != k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_270,plain,
    ( k2_relat_1(k6_relat_1(X0)) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_739,plain,
    ( k6_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(light_normalisation,[status(thm)],[c_270,c_8])).

cnf(c_1223,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_739])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1330,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1223,c_9])).

cnf(c_1551,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_1035,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_714])).

cnf(c_1727,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1035])).

cnf(c_2544,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2068,c_69,c_70,c_302,c_904,c_905,c_913,c_914,c_929,c_1033,c_1330,c_1551,c_1727,c_1732])).

cnf(c_1761,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1727,c_929,c_1551,c_1732])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_718,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1766,plain,
    ( k9_relat_1(k6_relat_1(k1_xboole_0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1761,c_718])).

cnf(c_1767,plain,
    ( k9_relat_1(k1_xboole_0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1766,c_1223])).

cnf(c_5,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1768,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1767,c_5])).

cnf(c_716,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1639,plain,
    ( k1_relset_1(X0,X1,sK1) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_716])).

cnf(c_1725,plain,
    ( k1_relset_1(k1_relat_1(sK1),X0,sK1) = k1_relat_1(sK1)
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1639])).

cnf(c_1838,plain,
    ( k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1549,c_1725])).

cnf(c_1331,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1223,c_8])).

cnf(c_2417,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1838,c_1330,c_1331,c_1768])).

cnf(c_2546,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2544,c_1768,c_2417])).

cnf(c_2547,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2546])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.89/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.00  
% 1.89/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.89/1.00  
% 1.89/1.00  ------  iProver source info
% 1.89/1.00  
% 1.89/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.89/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.89/1.00  git: non_committed_changes: false
% 1.89/1.00  git: last_make_outside_of_git: false
% 1.89/1.00  
% 1.89/1.00  ------ 
% 1.89/1.00  
% 1.89/1.00  ------ Input Options
% 1.89/1.00  
% 1.89/1.00  --out_options                           all
% 1.89/1.00  --tptp_safe_out                         true
% 1.89/1.00  --problem_path                          ""
% 1.89/1.00  --include_path                          ""
% 1.89/1.00  --clausifier                            res/vclausify_rel
% 1.89/1.00  --clausifier_options                    --mode clausify
% 1.89/1.00  --stdin                                 false
% 1.89/1.00  --stats_out                             all
% 1.89/1.00  
% 1.89/1.00  ------ General Options
% 1.89/1.00  
% 1.89/1.00  --fof                                   false
% 1.89/1.00  --time_out_real                         305.
% 1.89/1.00  --time_out_virtual                      -1.
% 1.89/1.00  --symbol_type_check                     false
% 1.89/1.00  --clausify_out                          false
% 1.89/1.00  --sig_cnt_out                           false
% 1.89/1.00  --trig_cnt_out                          false
% 1.89/1.00  --trig_cnt_out_tolerance                1.
% 1.89/1.00  --trig_cnt_out_sk_spl                   false
% 1.89/1.00  --abstr_cl_out                          false
% 1.89/1.00  
% 1.89/1.00  ------ Global Options
% 1.89/1.00  
% 1.89/1.00  --schedule                              default
% 1.89/1.00  --add_important_lit                     false
% 1.89/1.00  --prop_solver_per_cl                    1000
% 1.89/1.00  --min_unsat_core                        false
% 1.89/1.00  --soft_assumptions                      false
% 1.89/1.00  --soft_lemma_size                       3
% 1.89/1.00  --prop_impl_unit_size                   0
% 1.89/1.00  --prop_impl_unit                        []
% 1.89/1.00  --share_sel_clauses                     true
% 1.89/1.00  --reset_solvers                         false
% 1.89/1.00  --bc_imp_inh                            [conj_cone]
% 1.89/1.00  --conj_cone_tolerance                   3.
% 1.89/1.00  --extra_neg_conj                        none
% 1.89/1.00  --large_theory_mode                     true
% 1.89/1.00  --prolific_symb_bound                   200
% 1.89/1.00  --lt_threshold                          2000
% 1.89/1.00  --clause_weak_htbl                      true
% 1.89/1.00  --gc_record_bc_elim                     false
% 1.89/1.00  
% 1.89/1.00  ------ Preprocessing Options
% 1.89/1.00  
% 1.89/1.00  --preprocessing_flag                    true
% 1.89/1.00  --time_out_prep_mult                    0.1
% 1.89/1.00  --splitting_mode                        input
% 1.89/1.00  --splitting_grd                         true
% 1.89/1.00  --splitting_cvd                         false
% 1.89/1.00  --splitting_cvd_svl                     false
% 1.89/1.00  --splitting_nvd                         32
% 1.89/1.00  --sub_typing                            true
% 1.89/1.00  --prep_gs_sim                           true
% 1.89/1.00  --prep_unflatten                        true
% 1.89/1.00  --prep_res_sim                          true
% 1.89/1.00  --prep_upred                            true
% 1.89/1.00  --prep_sem_filter                       exhaustive
% 1.89/1.00  --prep_sem_filter_out                   false
% 1.89/1.00  --pred_elim                             true
% 1.89/1.00  --res_sim_input                         true
% 1.89/1.00  --eq_ax_congr_red                       true
% 1.89/1.00  --pure_diseq_elim                       true
% 1.89/1.00  --brand_transform                       false
% 1.89/1.00  --non_eq_to_eq                          false
% 1.89/1.00  --prep_def_merge                        true
% 1.89/1.00  --prep_def_merge_prop_impl              false
% 1.89/1.00  --prep_def_merge_mbd                    true
% 1.89/1.00  --prep_def_merge_tr_red                 false
% 1.89/1.00  --prep_def_merge_tr_cl                  false
% 1.89/1.00  --smt_preprocessing                     true
% 1.89/1.00  --smt_ac_axioms                         fast
% 1.89/1.00  --preprocessed_out                      false
% 1.89/1.00  --preprocessed_stats                    false
% 1.89/1.00  
% 1.89/1.00  ------ Abstraction refinement Options
% 1.89/1.00  
% 1.89/1.00  --abstr_ref                             []
% 1.89/1.00  --abstr_ref_prep                        false
% 1.89/1.00  --abstr_ref_until_sat                   false
% 1.89/1.00  --abstr_ref_sig_restrict                funpre
% 1.89/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/1.00  --abstr_ref_under                       []
% 1.89/1.00  
% 1.89/1.00  ------ SAT Options
% 1.89/1.00  
% 1.89/1.00  --sat_mode                              false
% 1.89/1.00  --sat_fm_restart_options                ""
% 1.89/1.00  --sat_gr_def                            false
% 1.89/1.00  --sat_epr_types                         true
% 1.89/1.00  --sat_non_cyclic_types                  false
% 1.89/1.00  --sat_finite_models                     false
% 1.89/1.00  --sat_fm_lemmas                         false
% 1.89/1.00  --sat_fm_prep                           false
% 1.89/1.00  --sat_fm_uc_incr                        true
% 1.89/1.00  --sat_out_model                         small
% 1.89/1.00  --sat_out_clauses                       false
% 1.89/1.00  
% 1.89/1.00  ------ QBF Options
% 1.89/1.00  
% 1.89/1.00  --qbf_mode                              false
% 1.89/1.00  --qbf_elim_univ                         false
% 1.89/1.00  --qbf_dom_inst                          none
% 1.89/1.00  --qbf_dom_pre_inst                      false
% 1.89/1.00  --qbf_sk_in                             false
% 1.89/1.00  --qbf_pred_elim                         true
% 1.89/1.00  --qbf_split                             512
% 1.89/1.00  
% 1.89/1.00  ------ BMC1 Options
% 1.89/1.00  
% 1.89/1.00  --bmc1_incremental                      false
% 1.89/1.00  --bmc1_axioms                           reachable_all
% 1.89/1.00  --bmc1_min_bound                        0
% 1.89/1.00  --bmc1_max_bound                        -1
% 1.89/1.00  --bmc1_max_bound_default                -1
% 1.89/1.00  --bmc1_symbol_reachability              true
% 1.89/1.00  --bmc1_property_lemmas                  false
% 1.89/1.00  --bmc1_k_induction                      false
% 1.89/1.00  --bmc1_non_equiv_states                 false
% 1.89/1.00  --bmc1_deadlock                         false
% 1.89/1.00  --bmc1_ucm                              false
% 1.89/1.00  --bmc1_add_unsat_core                   none
% 1.89/1.00  --bmc1_unsat_core_children              false
% 1.89/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/1.00  --bmc1_out_stat                         full
% 1.89/1.00  --bmc1_ground_init                      false
% 1.89/1.00  --bmc1_pre_inst_next_state              false
% 1.89/1.00  --bmc1_pre_inst_state                   false
% 1.89/1.00  --bmc1_pre_inst_reach_state             false
% 1.89/1.00  --bmc1_out_unsat_core                   false
% 1.89/1.00  --bmc1_aig_witness_out                  false
% 1.89/1.00  --bmc1_verbose                          false
% 1.89/1.00  --bmc1_dump_clauses_tptp                false
% 1.89/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.89/1.00  --bmc1_dump_file                        -
% 1.89/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.89/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.89/1.00  --bmc1_ucm_extend_mode                  1
% 1.89/1.00  --bmc1_ucm_init_mode                    2
% 1.89/1.00  --bmc1_ucm_cone_mode                    none
% 1.89/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.89/1.00  --bmc1_ucm_relax_model                  4
% 1.89/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.89/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/1.00  --bmc1_ucm_layered_model                none
% 1.89/1.00  --bmc1_ucm_max_lemma_size               10
% 1.89/1.00  
% 1.89/1.00  ------ AIG Options
% 1.89/1.00  
% 1.89/1.00  --aig_mode                              false
% 1.89/1.00  
% 1.89/1.00  ------ Instantiation Options
% 1.89/1.00  
% 1.89/1.00  --instantiation_flag                    true
% 1.89/1.00  --inst_sos_flag                         false
% 1.89/1.00  --inst_sos_phase                        true
% 1.89/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/1.00  --inst_lit_sel_side                     num_symb
% 1.89/1.00  --inst_solver_per_active                1400
% 1.89/1.00  --inst_solver_calls_frac                1.
% 1.89/1.00  --inst_passive_queue_type               priority_queues
% 1.89/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/1.00  --inst_passive_queues_freq              [25;2]
% 1.89/1.00  --inst_dismatching                      true
% 1.89/1.00  --inst_eager_unprocessed_to_passive     true
% 1.89/1.00  --inst_prop_sim_given                   true
% 1.89/1.00  --inst_prop_sim_new                     false
% 1.89/1.00  --inst_subs_new                         false
% 1.89/1.00  --inst_eq_res_simp                      false
% 1.89/1.00  --inst_subs_given                       false
% 1.89/1.00  --inst_orphan_elimination               true
% 1.89/1.00  --inst_learning_loop_flag               true
% 1.89/1.00  --inst_learning_start                   3000
% 1.89/1.00  --inst_learning_factor                  2
% 1.89/1.00  --inst_start_prop_sim_after_learn       3
% 1.89/1.00  --inst_sel_renew                        solver
% 1.89/1.00  --inst_lit_activity_flag                true
% 1.89/1.00  --inst_restr_to_given                   false
% 1.89/1.00  --inst_activity_threshold               500
% 1.89/1.00  --inst_out_proof                        true
% 1.89/1.00  
% 1.89/1.00  ------ Resolution Options
% 1.89/1.00  
% 1.89/1.00  --resolution_flag                       true
% 1.89/1.00  --res_lit_sel                           adaptive
% 1.89/1.00  --res_lit_sel_side                      none
% 1.89/1.00  --res_ordering                          kbo
% 1.89/1.00  --res_to_prop_solver                    active
% 1.89/1.00  --res_prop_simpl_new                    false
% 1.89/1.00  --res_prop_simpl_given                  true
% 1.89/1.00  --res_passive_queue_type                priority_queues
% 1.89/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/1.00  --res_passive_queues_freq               [15;5]
% 1.89/1.00  --res_forward_subs                      full
% 1.89/1.00  --res_backward_subs                     full
% 1.89/1.00  --res_forward_subs_resolution           true
% 1.89/1.00  --res_backward_subs_resolution          true
% 1.89/1.00  --res_orphan_elimination                true
% 1.89/1.00  --res_time_limit                        2.
% 1.89/1.00  --res_out_proof                         true
% 1.89/1.00  
% 1.89/1.00  ------ Superposition Options
% 1.89/1.00  
% 1.89/1.00  --superposition_flag                    true
% 1.89/1.00  --sup_passive_queue_type                priority_queues
% 1.89/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.89/1.00  --demod_completeness_check              fast
% 1.89/1.00  --demod_use_ground                      true
% 1.89/1.00  --sup_to_prop_solver                    passive
% 1.89/1.00  --sup_prop_simpl_new                    true
% 1.89/1.00  --sup_prop_simpl_given                  true
% 1.89/1.00  --sup_fun_splitting                     false
% 1.89/1.00  --sup_smt_interval                      50000
% 1.89/1.00  
% 1.89/1.00  ------ Superposition Simplification Setup
% 1.89/1.00  
% 1.89/1.00  --sup_indices_passive                   []
% 1.89/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.00  --sup_full_bw                           [BwDemod]
% 1.89/1.00  --sup_immed_triv                        [TrivRules]
% 1.89/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.00  --sup_immed_bw_main                     []
% 1.89/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.00  
% 1.89/1.00  ------ Combination Options
% 1.89/1.00  
% 1.89/1.00  --comb_res_mult                         3
% 1.89/1.00  --comb_sup_mult                         2
% 1.89/1.00  --comb_inst_mult                        10
% 1.89/1.00  
% 1.89/1.00  ------ Debug Options
% 1.89/1.00  
% 1.89/1.00  --dbg_backtrace                         false
% 1.89/1.00  --dbg_dump_prop_clauses                 false
% 1.89/1.00  --dbg_dump_prop_clauses_file            -
% 1.89/1.00  --dbg_out_stat                          false
% 1.89/1.00  ------ Parsing...
% 1.89/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.89/1.00  
% 1.89/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.89/1.00  
% 1.89/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.89/1.00  
% 1.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.89/1.00  ------ Proving...
% 1.89/1.00  ------ Problem Properties 
% 1.89/1.00  
% 1.89/1.00  
% 1.89/1.00  clauses                                 20
% 1.89/1.00  conjectures                             0
% 1.89/1.00  EPR                                     0
% 1.89/1.00  Horn                                    18
% 1.89/1.00  unary                                   5
% 1.89/1.00  binary                                  10
% 1.89/1.00  lits                                    43
% 1.89/1.00  lits eq                                 24
% 1.89/1.00  fd_pure                                 0
% 1.89/1.00  fd_pseudo                               0
% 1.89/1.00  fd_cond                                 1
% 1.89/1.00  fd_pseudo_cond                          0
% 1.89/1.00  AC symbols                              0
% 1.89/1.00  
% 1.89/1.00  ------ Schedule dynamic 5 is on 
% 1.89/1.00  
% 1.89/1.00  ------ no conjectures: strip conj schedule 
% 1.89/1.00  
% 1.89/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.89/1.00  
% 1.89/1.00  
% 1.89/1.00  ------ 
% 1.89/1.00  Current options:
% 1.89/1.00  ------ 
% 1.89/1.00  
% 1.89/1.00  ------ Input Options
% 1.89/1.00  
% 1.89/1.00  --out_options                           all
% 1.89/1.00  --tptp_safe_out                         true
% 1.89/1.00  --problem_path                          ""
% 1.89/1.00  --include_path                          ""
% 1.89/1.00  --clausifier                            res/vclausify_rel
% 1.89/1.00  --clausifier_options                    --mode clausify
% 1.89/1.00  --stdin                                 false
% 1.89/1.00  --stats_out                             all
% 1.89/1.00  
% 1.89/1.00  ------ General Options
% 1.89/1.00  
% 1.89/1.00  --fof                                   false
% 1.89/1.00  --time_out_real                         305.
% 1.89/1.00  --time_out_virtual                      -1.
% 1.89/1.00  --symbol_type_check                     false
% 1.89/1.00  --clausify_out                          false
% 1.89/1.00  --sig_cnt_out                           false
% 1.89/1.00  --trig_cnt_out                          false
% 1.89/1.00  --trig_cnt_out_tolerance                1.
% 1.89/1.00  --trig_cnt_out_sk_spl                   false
% 1.89/1.00  --abstr_cl_out                          false
% 1.89/1.00  
% 1.89/1.00  ------ Global Options
% 1.89/1.00  
% 1.89/1.00  --schedule                              default
% 1.89/1.00  --add_important_lit                     false
% 1.89/1.00  --prop_solver_per_cl                    1000
% 1.89/1.00  --min_unsat_core                        false
% 1.89/1.00  --soft_assumptions                      false
% 1.89/1.00  --soft_lemma_size                       3
% 1.89/1.00  --prop_impl_unit_size                   0
% 1.89/1.00  --prop_impl_unit                        []
% 1.89/1.00  --share_sel_clauses                     true
% 1.89/1.00  --reset_solvers                         false
% 1.89/1.00  --bc_imp_inh                            [conj_cone]
% 1.89/1.00  --conj_cone_tolerance                   3.
% 1.89/1.00  --extra_neg_conj                        none
% 1.89/1.00  --large_theory_mode                     true
% 1.89/1.00  --prolific_symb_bound                   200
% 1.89/1.00  --lt_threshold                          2000
% 1.89/1.00  --clause_weak_htbl                      true
% 1.89/1.00  --gc_record_bc_elim                     false
% 1.89/1.00  
% 1.89/1.00  ------ Preprocessing Options
% 1.89/1.00  
% 1.89/1.00  --preprocessing_flag                    true
% 1.89/1.00  --time_out_prep_mult                    0.1
% 1.89/1.00  --splitting_mode                        input
% 1.89/1.00  --splitting_grd                         true
% 1.89/1.00  --splitting_cvd                         false
% 1.89/1.00  --splitting_cvd_svl                     false
% 1.89/1.00  --splitting_nvd                         32
% 1.89/1.00  --sub_typing                            true
% 1.89/1.00  --prep_gs_sim                           true
% 1.89/1.00  --prep_unflatten                        true
% 1.89/1.00  --prep_res_sim                          true
% 1.89/1.00  --prep_upred                            true
% 1.89/1.00  --prep_sem_filter                       exhaustive
% 1.89/1.00  --prep_sem_filter_out                   false
% 1.89/1.00  --pred_elim                             true
% 1.89/1.00  --res_sim_input                         true
% 1.89/1.00  --eq_ax_congr_red                       true
% 1.89/1.00  --pure_diseq_elim                       true
% 1.89/1.00  --brand_transform                       false
% 1.89/1.00  --non_eq_to_eq                          false
% 1.89/1.00  --prep_def_merge                        true
% 1.89/1.00  --prep_def_merge_prop_impl              false
% 1.89/1.00  --prep_def_merge_mbd                    true
% 1.89/1.00  --prep_def_merge_tr_red                 false
% 1.89/1.00  --prep_def_merge_tr_cl                  false
% 1.89/1.00  --smt_preprocessing                     true
% 1.89/1.00  --smt_ac_axioms                         fast
% 1.89/1.00  --preprocessed_out                      false
% 1.89/1.00  --preprocessed_stats                    false
% 1.89/1.00  
% 1.89/1.00  ------ Abstraction refinement Options
% 1.89/1.00  
% 1.89/1.00  --abstr_ref                             []
% 1.89/1.00  --abstr_ref_prep                        false
% 1.89/1.00  --abstr_ref_until_sat                   false
% 1.89/1.00  --abstr_ref_sig_restrict                funpre
% 1.89/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/1.00  --abstr_ref_under                       []
% 1.89/1.00  
% 1.89/1.00  ------ SAT Options
% 1.89/1.01  
% 1.89/1.01  --sat_mode                              false
% 1.89/1.01  --sat_fm_restart_options                ""
% 1.89/1.01  --sat_gr_def                            false
% 1.89/1.01  --sat_epr_types                         true
% 1.89/1.01  --sat_non_cyclic_types                  false
% 1.89/1.01  --sat_finite_models                     false
% 1.89/1.01  --sat_fm_lemmas                         false
% 1.89/1.01  --sat_fm_prep                           false
% 1.89/1.01  --sat_fm_uc_incr                        true
% 1.89/1.01  --sat_out_model                         small
% 1.89/1.01  --sat_out_clauses                       false
% 1.89/1.01  
% 1.89/1.01  ------ QBF Options
% 1.89/1.01  
% 1.89/1.01  --qbf_mode                              false
% 1.89/1.01  --qbf_elim_univ                         false
% 1.89/1.01  --qbf_dom_inst                          none
% 1.89/1.01  --qbf_dom_pre_inst                      false
% 1.89/1.01  --qbf_sk_in                             false
% 1.89/1.01  --qbf_pred_elim                         true
% 1.89/1.01  --qbf_split                             512
% 1.89/1.01  
% 1.89/1.01  ------ BMC1 Options
% 1.89/1.01  
% 1.89/1.01  --bmc1_incremental                      false
% 1.89/1.01  --bmc1_axioms                           reachable_all
% 1.89/1.01  --bmc1_min_bound                        0
% 1.89/1.01  --bmc1_max_bound                        -1
% 1.89/1.01  --bmc1_max_bound_default                -1
% 1.89/1.01  --bmc1_symbol_reachability              true
% 1.89/1.01  --bmc1_property_lemmas                  false
% 1.89/1.01  --bmc1_k_induction                      false
% 1.89/1.01  --bmc1_non_equiv_states                 false
% 1.89/1.01  --bmc1_deadlock                         false
% 1.89/1.01  --bmc1_ucm                              false
% 1.89/1.01  --bmc1_add_unsat_core                   none
% 1.89/1.01  --bmc1_unsat_core_children              false
% 1.89/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/1.01  --bmc1_out_stat                         full
% 1.89/1.01  --bmc1_ground_init                      false
% 1.89/1.01  --bmc1_pre_inst_next_state              false
% 1.89/1.01  --bmc1_pre_inst_state                   false
% 1.89/1.01  --bmc1_pre_inst_reach_state             false
% 1.89/1.01  --bmc1_out_unsat_core                   false
% 1.89/1.01  --bmc1_aig_witness_out                  false
% 1.89/1.01  --bmc1_verbose                          false
% 1.89/1.01  --bmc1_dump_clauses_tptp                false
% 1.89/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.89/1.01  --bmc1_dump_file                        -
% 1.89/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.89/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.89/1.01  --bmc1_ucm_extend_mode                  1
% 1.89/1.01  --bmc1_ucm_init_mode                    2
% 1.89/1.01  --bmc1_ucm_cone_mode                    none
% 1.89/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.89/1.01  --bmc1_ucm_relax_model                  4
% 1.89/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.89/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/1.01  --bmc1_ucm_layered_model                none
% 1.89/1.01  --bmc1_ucm_max_lemma_size               10
% 1.89/1.01  
% 1.89/1.01  ------ AIG Options
% 1.89/1.01  
% 1.89/1.01  --aig_mode                              false
% 1.89/1.01  
% 1.89/1.01  ------ Instantiation Options
% 1.89/1.01  
% 1.89/1.01  --instantiation_flag                    true
% 1.89/1.01  --inst_sos_flag                         false
% 1.89/1.01  --inst_sos_phase                        true
% 1.89/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/1.01  --inst_lit_sel_side                     none
% 1.89/1.01  --inst_solver_per_active                1400
% 1.89/1.01  --inst_solver_calls_frac                1.
% 1.89/1.01  --inst_passive_queue_type               priority_queues
% 1.89/1.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.89/1.01  --inst_passive_queues_freq              [25;2]
% 1.89/1.01  --inst_dismatching                      true
% 1.89/1.01  --inst_eager_unprocessed_to_passive     true
% 1.89/1.01  --inst_prop_sim_given                   true
% 1.89/1.01  --inst_prop_sim_new                     false
% 1.89/1.01  --inst_subs_new                         false
% 1.89/1.01  --inst_eq_res_simp                      false
% 1.89/1.01  --inst_subs_given                       false
% 1.89/1.01  --inst_orphan_elimination               true
% 1.89/1.01  --inst_learning_loop_flag               true
% 1.89/1.01  --inst_learning_start                   3000
% 1.89/1.01  --inst_learning_factor                  2
% 1.89/1.01  --inst_start_prop_sim_after_learn       3
% 1.89/1.01  --inst_sel_renew                        solver
% 1.89/1.01  --inst_lit_activity_flag                true
% 1.89/1.01  --inst_restr_to_given                   false
% 1.89/1.01  --inst_activity_threshold               500
% 1.89/1.01  --inst_out_proof                        true
% 1.89/1.01  
% 1.89/1.01  ------ Resolution Options
% 1.89/1.01  
% 1.89/1.01  --resolution_flag                       false
% 1.89/1.01  --res_lit_sel                           adaptive
% 1.89/1.01  --res_lit_sel_side                      none
% 1.89/1.01  --res_ordering                          kbo
% 1.89/1.01  --res_to_prop_solver                    active
% 1.89/1.01  --res_prop_simpl_new                    false
% 1.89/1.01  --res_prop_simpl_given                  true
% 1.89/1.01  --res_passive_queue_type                priority_queues
% 1.89/1.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.89/1.01  --res_passive_queues_freq               [15;5]
% 1.89/1.01  --res_forward_subs                      full
% 1.89/1.01  --res_backward_subs                     full
% 1.89/1.01  --res_forward_subs_resolution           true
% 1.89/1.01  --res_backward_subs_resolution          true
% 1.89/1.01  --res_orphan_elimination                true
% 1.89/1.01  --res_time_limit                        2.
% 1.89/1.01  --res_out_proof                         true
% 1.89/1.01  
% 1.89/1.01  ------ Superposition Options
% 1.89/1.01  
% 1.89/1.01  --superposition_flag                    true
% 1.89/1.01  --sup_passive_queue_type                priority_queues
% 1.89/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.89/1.01  --demod_completeness_check              fast
% 1.89/1.01  --demod_use_ground                      true
% 1.89/1.01  --sup_to_prop_solver                    passive
% 1.89/1.01  --sup_prop_simpl_new                    true
% 1.89/1.01  --sup_prop_simpl_given                  true
% 1.89/1.01  --sup_fun_splitting                     false
% 1.89/1.01  --sup_smt_interval                      50000
% 1.89/1.01  
% 1.89/1.01  ------ Superposition Simplification Setup
% 1.89/1.01  
% 1.89/1.01  --sup_indices_passive                   []
% 1.89/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_full_bw                           [BwDemod]
% 1.89/1.01  --sup_immed_triv                        [TrivRules]
% 1.89/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_immed_bw_main                     []
% 1.89/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.01  
% 1.89/1.01  ------ Combination Options
% 1.89/1.01  
% 1.89/1.01  --comb_res_mult                         3
% 1.89/1.01  --comb_sup_mult                         2
% 1.89/1.01  --comb_inst_mult                        10
% 1.89/1.01  
% 1.89/1.01  ------ Debug Options
% 1.89/1.01  
% 1.89/1.01  --dbg_backtrace                         false
% 1.89/1.01  --dbg_dump_prop_clauses                 false
% 1.89/1.01  --dbg_dump_prop_clauses_file            -
% 1.89/1.01  --dbg_out_stat                          false
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  ------ Proving...
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  % SZS status Theorem for theBenchmark.p
% 1.89/1.01  
% 1.89/1.01   Resolution empty clause
% 1.89/1.01  
% 1.89/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.89/1.01  
% 1.89/1.01  fof(f1,axiom,(
% 1.89/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f14,plain,(
% 1.89/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.89/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 1.89/1.01  
% 1.89/1.01  fof(f16,plain,(
% 1.89/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f14])).
% 1.89/1.01  
% 1.89/1.01  fof(f28,plain,(
% 1.89/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.89/1.01    introduced(choice_axiom,[])).
% 1.89/1.01  
% 1.89/1.01  fof(f29,plain,(
% 1.89/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).
% 1.89/1.01  
% 1.89/1.01  fof(f35,plain,(
% 1.89/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f29])).
% 1.89/1.01  
% 1.89/1.01  fof(f36,plain,(
% 1.89/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f29])).
% 1.89/1.01  
% 1.89/1.01  fof(f10,axiom,(
% 1.89/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f22,plain,(
% 1.89/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.89/1.01    inference(ennf_transformation,[],[f10])).
% 1.89/1.01  
% 1.89/1.01  fof(f23,plain,(
% 1.89/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.89/1.01    inference(flattening,[],[f22])).
% 1.89/1.01  
% 1.89/1.01  fof(f49,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f23])).
% 1.89/1.01  
% 1.89/1.01  fof(f12,conjecture,(
% 1.89/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f13,negated_conjecture,(
% 1.89/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.89/1.01    inference(negated_conjecture,[],[f12])).
% 1.89/1.01  
% 1.89/1.01  fof(f26,plain,(
% 1.89/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f13])).
% 1.89/1.01  
% 1.89/1.01  fof(f27,plain,(
% 1.89/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.89/1.01    inference(flattening,[],[f26])).
% 1.89/1.01  
% 1.89/1.01  fof(f33,plain,(
% 1.89/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.89/1.01    introduced(choice_axiom,[])).
% 1.89/1.01  
% 1.89/1.01  fof(f34,plain,(
% 1.89/1.01    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f33])).
% 1.89/1.01  
% 1.89/1.01  fof(f56,plain,(
% 1.89/1.01    v1_relat_1(sK1)),
% 1.89/1.01    inference(cnf_transformation,[],[f34])).
% 1.89/1.01  
% 1.89/1.01  fof(f11,axiom,(
% 1.89/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f24,plain,(
% 1.89/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/1.01    inference(ennf_transformation,[],[f11])).
% 1.89/1.01  
% 1.89/1.01  fof(f25,plain,(
% 1.89/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/1.01    inference(flattening,[],[f24])).
% 1.89/1.01  
% 1.89/1.01  fof(f32,plain,(
% 1.89/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/1.01    inference(nnf_transformation,[],[f25])).
% 1.89/1.01  
% 1.89/1.01  fof(f52,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/1.01    inference(cnf_transformation,[],[f32])).
% 1.89/1.01  
% 1.89/1.01  fof(f58,plain,(
% 1.89/1.01    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 1.89/1.01    inference(cnf_transformation,[],[f34])).
% 1.89/1.01  
% 1.89/1.01  fof(f57,plain,(
% 1.89/1.01    v1_funct_1(sK1)),
% 1.89/1.01    inference(cnf_transformation,[],[f34])).
% 1.89/1.01  
% 1.89/1.01  fof(f9,axiom,(
% 1.89/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f21,plain,(
% 1.89/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/1.01    inference(ennf_transformation,[],[f9])).
% 1.89/1.01  
% 1.89/1.01  fof(f48,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/1.01    inference(cnf_transformation,[],[f21])).
% 1.89/1.01  
% 1.89/1.01  fof(f53,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/1.01    inference(cnf_transformation,[],[f32])).
% 1.89/1.01  
% 1.89/1.01  fof(f64,plain,(
% 1.89/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.89/1.01    inference(equality_resolution,[],[f53])).
% 1.89/1.01  
% 1.89/1.01  fof(f2,axiom,(
% 1.89/1.01    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f30,plain,(
% 1.89/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.89/1.01    inference(nnf_transformation,[],[f2])).
% 1.89/1.01  
% 1.89/1.01  fof(f31,plain,(
% 1.89/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.89/1.01    inference(flattening,[],[f30])).
% 1.89/1.01  
% 1.89/1.01  fof(f38,plain,(
% 1.89/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f60,plain,(
% 1.89/1.01    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 1.89/1.01    inference(equality_resolution,[],[f38])).
% 1.89/1.01  
% 1.89/1.01  fof(f39,plain,(
% 1.89/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f59,plain,(
% 1.89/1.01    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.89/1.01    inference(equality_resolution,[],[f39])).
% 1.89/1.01  
% 1.89/1.01  fof(f37,plain,(
% 1.89/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f4,axiom,(
% 1.89/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f17,plain,(
% 1.89/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.89/1.01    inference(ennf_transformation,[],[f4])).
% 1.89/1.01  
% 1.89/1.01  fof(f18,plain,(
% 1.89/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.89/1.01    inference(flattening,[],[f17])).
% 1.89/1.01  
% 1.89/1.01  fof(f42,plain,(
% 1.89/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f18])).
% 1.89/1.01  
% 1.89/1.01  fof(f6,axiom,(
% 1.89/1.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f15,plain,(
% 1.89/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.89/1.01    inference(pure_predicate_removal,[],[f6])).
% 1.89/1.01  
% 1.89/1.01  fof(f45,plain,(
% 1.89/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.89/1.01    inference(cnf_transformation,[],[f15])).
% 1.89/1.01  
% 1.89/1.01  fof(f5,axiom,(
% 1.89/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f44,plain,(
% 1.89/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.89/1.01    inference(cnf_transformation,[],[f5])).
% 1.89/1.01  
% 1.89/1.01  fof(f43,plain,(
% 1.89/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.89/1.01    inference(cnf_transformation,[],[f5])).
% 1.89/1.01  
% 1.89/1.01  fof(f7,axiom,(
% 1.89/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f19,plain,(
% 1.89/1.01    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f7])).
% 1.89/1.01  
% 1.89/1.01  fof(f46,plain,(
% 1.89/1.01    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/1.01    inference(cnf_transformation,[],[f19])).
% 1.89/1.01  
% 1.89/1.01  fof(f3,axiom,(
% 1.89/1.01    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f40,plain,(
% 1.89/1.01    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f3])).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1,plain,
% 1.89/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_719,plain,
% 1.89/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.89/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_0,plain,
% 1.89/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_720,plain,
% 1.89/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 1.89/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1549,plain,
% 1.89/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_719,c_720]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_14,plain,
% 1.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.89/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.89/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.89/1.01      | ~ v1_relat_1(X0) ),
% 1.89/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_23,negated_conjecture,
% 1.89/1.01      ( v1_relat_1(sK1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_278,plain,
% 1.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.89/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.89/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.89/1.01      | sK1 != X0 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_279,plain,
% 1.89/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.89/1.01      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 1.89/1.01      | ~ r1_tarski(k2_relat_1(sK1),X1) ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_278]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_714,plain,
% 1.89/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 1.89/1.01      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_18,plain,
% 1.89/1.01      ( v1_funct_2(X0,X1,X2)
% 1.89/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.89/1.01      | k1_relset_1(X1,X2,X0) != X1
% 1.89/1.01      | k1_xboole_0 = X2 ),
% 1.89/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_21,negated_conjecture,
% 1.89/1.01      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
% 1.89/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.89/1.01      | ~ v1_funct_1(sK1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_22,negated_conjecture,
% 1.89/1.01      ( v1_funct_1(sK1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_116,plain,
% 1.89/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.89/1.01      | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
% 1.89/1.01      inference(global_propositional_subsumption,[status(thm)],[c_21,c_22]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_117,negated_conjecture,
% 1.89/1.01      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
% 1.89/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
% 1.89/1.01      inference(renaming,[status(thm)],[c_116]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_376,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.89/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.89/1.01      | k1_relset_1(X1,X2,X0) != X1
% 1.89/1.01      | k1_relat_1(sK1) != X1
% 1.89/1.01      | k2_relat_1(sK1) != X2
% 1.89/1.01      | sK1 != X0
% 1.89/1.01      | k1_xboole_0 = X2 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_117]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_377,plain,
% 1.89/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.89/1.01      | k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) != k1_relat_1(sK1)
% 1.89/1.01      | k1_xboole_0 = k2_relat_1(sK1) ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_376]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_13,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.89/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.89/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_385,plain,
% 1.89/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.89/1.01      | k1_xboole_0 = k2_relat_1(sK1) ),
% 1.89/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_377,c_13]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_711,plain,
% 1.89/1.01      ( k1_xboole_0 = k2_relat_1(sK1)
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_855,plain,
% 1.89/1.01      ( k2_relat_1(sK1) = k1_xboole_0
% 1.89/1.01      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) != iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_714,c_711]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1729,plain,
% 1.89/1.01      ( k2_relat_1(sK1) = k1_xboole_0
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) != iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1549,c_855]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1732,plain,
% 1.89/1.01      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 1.89/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1729,c_1549]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_17,plain,
% 1.89/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.89/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.89/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_360,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.89/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.89/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.89/1.01      | k1_relat_1(sK1) != k1_xboole_0
% 1.89/1.01      | k2_relat_1(sK1) != X1
% 1.89/1.01      | sK1 != X0 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_117]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_361,plain,
% 1.89/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.89/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1))))
% 1.89/1.01      | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 1.89/1.01      | k1_relat_1(sK1) != k1_xboole_0 ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_360]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_712,plain,
% 1.89/1.01      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 1.89/1.01      | k1_relat_1(sK1) != k1_xboole_0
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1)))) != iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_3,plain,
% 1.89/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_788,plain,
% 1.89/1.01      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 1.89/1.01      | k1_relat_1(sK1) != k1_xboole_0
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.89/1.01      inference(demodulation,[status(thm)],[c_712,c_3]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2053,plain,
% 1.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.89/1.01      | k1_relat_1(sK1) != k1_xboole_0
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.89/1.01      inference(demodulation,[status(thm)],[c_1732,c_788]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2,plain,
% 1.89/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2068,plain,
% 1.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.89/1.01      | k1_relat_1(sK1) != k1_xboole_0
% 1.89/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.89/1.01      inference(demodulation,[status(thm)],[c_2053,c_2]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_4,plain,
% 1.89/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.89/1.01      | k1_xboole_0 = X1
% 1.89/1.01      | k1_xboole_0 = X0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_69,plain,
% 1.89/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.89/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_70,plain,
% 1.89/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_6,plain,
% 1.89/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_301,plain,
% 1.89/1.01      ( k2_relat_1(X0) != k1_xboole_0 | sK1 != X0 | k1_xboole_0 = X0 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_302,plain,
% 1.89/1.01      ( k2_relat_1(sK1) != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_301]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_499,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_857,plain,
% 1.89/1.01      ( k1_relat_1(sK1) != X0
% 1.89/1.01      | k1_relat_1(sK1) = k1_xboole_0
% 1.89/1.01      | k1_xboole_0 != X0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_499]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_902,plain,
% 1.89/1.01      ( k1_relat_1(sK1) != k1_relat_1(X0)
% 1.89/1.01      | k1_relat_1(sK1) = k1_xboole_0
% 1.89/1.01      | k1_xboole_0 != k1_relat_1(X0) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_857]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_904,plain,
% 1.89/1.01      ( k1_relat_1(sK1) != k1_relat_1(k1_xboole_0)
% 1.89/1.01      | k1_relat_1(sK1) = k1_xboole_0
% 1.89/1.01      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_902]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_505,plain,
% 1.89/1.01      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 1.89/1.01      theory(equality) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_903,plain,
% 1.89/1.01      ( k1_relat_1(sK1) = k1_relat_1(X0) | sK1 != X0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_505]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_905,plain,
% 1.89/1.01      ( k1_relat_1(sK1) = k1_relat_1(k1_xboole_0) | sK1 != k1_xboole_0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_903]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_859,plain,
% 1.89/1.01      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_499]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_913,plain,
% 1.89/1.01      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_859]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_498,plain,( X0 = X0 ),theory(equality) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_914,plain,
% 1.89/1.01      ( sK1 = sK1 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_498]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_500,plain,
% 1.89/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 1.89/1.01      theory(equality) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_926,plain,
% 1.89/1.01      ( ~ r1_tarski(X0,X1)
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),X1)
% 1.89/1.01      | k2_relat_1(sK1) != X0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_500]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_927,plain,
% 1.89/1.01      ( k2_relat_1(sK1) != X0
% 1.89/1.01      | r1_tarski(X0,X1) != iProver_top
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),X1) = iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_929,plain,
% 1.89/1.01      ( k2_relat_1(sK1) != k1_xboole_0
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top
% 1.89/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_927]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1032,plain,
% 1.89/1.01      ( k1_relat_1(X0) != X1
% 1.89/1.01      | k1_xboole_0 != X1
% 1.89/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_499]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1033,plain,
% 1.89/1.01      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 1.89/1.01      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 1.89/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_1032]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_10,plain,
% 1.89/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.89/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_269,plain,
% 1.89/1.01      ( k6_relat_1(X0) != X1
% 1.89/1.01      | k2_relat_1(X1) != k1_xboole_0
% 1.89/1.01      | k1_xboole_0 = X1 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_270,plain,
% 1.89/1.01      ( k2_relat_1(k6_relat_1(X0)) != k1_xboole_0
% 1.89/1.01      | k1_xboole_0 = k6_relat_1(X0) ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_269]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_8,plain,
% 1.89/1.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_739,plain,
% 1.89/1.01      ( k6_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.89/1.01      inference(light_normalisation,[status(thm)],[c_270,c_8]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1223,plain,
% 1.89/1.01      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.89/1.01      inference(equality_resolution,[status(thm)],[c_739]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_9,plain,
% 1.89/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1330,plain,
% 1.89/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1223,c_9]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1551,plain,
% 1.89/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_1549]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1035,plain,
% 1.89/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.89/1.01      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_2,c_714]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1727,plain,
% 1.89/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1549,c_1035]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2544,plain,
% 1.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0 ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_2068,c_69,c_70,c_302,c_904,c_905,c_913,c_914,c_929,c_1033,
% 1.89/1.01                 c_1330,c_1551,c_1727,c_1732]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1761,plain,
% 1.89/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_1727,c_929,c_1551,c_1732]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_11,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.89/1.01      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_718,plain,
% 1.89/1.01      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 1.89/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1766,plain,
% 1.89/1.01      ( k9_relat_1(k6_relat_1(k1_xboole_0),sK1) = sK1 ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1761,c_718]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1767,plain,
% 1.89/1.01      ( k9_relat_1(k1_xboole_0,sK1) = sK1 ),
% 1.89/1.01      inference(light_normalisation,[status(thm)],[c_1766,c_1223]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_5,plain,
% 1.89/1.01      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.89/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1768,plain,
% 1.89/1.01      ( sK1 = k1_xboole_0 ),
% 1.89/1.01      inference(demodulation,[status(thm)],[c_1767,c_5]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_716,plain,
% 1.89/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.89/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1639,plain,
% 1.89/1.01      ( k1_relset_1(X0,X1,sK1) = k1_relat_1(sK1)
% 1.89/1.01      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_714,c_716]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1725,plain,
% 1.89/1.01      ( k1_relset_1(k1_relat_1(sK1),X0,sK1) = k1_relat_1(sK1)
% 1.89/1.01      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1549,c_1639]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1838,plain,
% 1.89/1.01      ( k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) = k1_relat_1(sK1) ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1549,c_1725]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1331,plain,
% 1.89/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1223,c_8]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2417,plain,
% 1.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.89/1.01      inference(light_normalisation,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_1838,c_1330,c_1331,c_1768]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2546,plain,
% 1.89/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 1.89/1.01      inference(light_normalisation,[status(thm)],[c_2544,c_1768,c_2417]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2547,plain,
% 1.89/1.01      ( $false ),
% 1.89/1.01      inference(equality_resolution_simp,[status(thm)],[c_2546]) ).
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.89/1.01  
% 1.89/1.01  ------                               Statistics
% 1.89/1.01  
% 1.89/1.01  ------ General
% 1.89/1.01  
% 1.89/1.01  abstr_ref_over_cycles:                  0
% 1.89/1.01  abstr_ref_under_cycles:                 0
% 1.89/1.01  gc_basic_clause_elim:                   0
% 1.89/1.01  forced_gc_time:                         0
% 1.89/1.01  parsing_time:                           0.01
% 1.89/1.01  unif_index_cands_time:                  0.
% 1.89/1.01  unif_index_add_time:                    0.
% 1.89/1.01  orderings_time:                         0.
% 1.89/1.01  out_proof_time:                         0.008
% 1.89/1.01  total_time:                             0.098
% 1.89/1.01  num_of_symbols:                         47
% 1.89/1.01  num_of_terms:                           3205
% 1.89/1.01  
% 1.89/1.01  ------ Preprocessing
% 1.89/1.01  
% 1.89/1.01  num_of_splits:                          0
% 1.89/1.01  num_of_split_atoms:                     0
% 1.89/1.01  num_of_reused_defs:                     0
% 1.89/1.01  num_eq_ax_congr_red:                    20
% 1.89/1.01  num_of_sem_filtered_clauses:            2
% 1.89/1.01  num_of_subtypes:                        0
% 1.89/1.01  monotx_restored_types:                  0
% 1.89/1.01  sat_num_of_epr_types:                   0
% 1.89/1.01  sat_num_of_non_cyclic_types:            0
% 1.89/1.01  sat_guarded_non_collapsed_types:        0
% 1.89/1.01  num_pure_diseq_elim:                    0
% 1.89/1.01  simp_replaced_by:                       0
% 1.89/1.01  res_preprocessed:                       107
% 1.89/1.01  prep_upred:                             0
% 1.89/1.01  prep_unflattend:                        34
% 1.89/1.01  smt_new_axioms:                         0
% 1.89/1.01  pred_elim_cands:                        3
% 1.89/1.01  pred_elim:                              2
% 1.89/1.01  pred_elim_cl:                           3
% 1.89/1.01  pred_elim_cycles:                       5
% 1.89/1.01  merged_defs:                            0
% 1.89/1.01  merged_defs_ncl:                        0
% 1.89/1.01  bin_hyper_res:                          0
% 1.89/1.01  prep_cycles:                            4
% 1.89/1.01  pred_elim_time:                         0.004
% 1.89/1.01  splitting_time:                         0.
% 1.89/1.01  sem_filter_time:                        0.
% 1.89/1.01  monotx_time:                            0.
% 1.89/1.01  subtype_inf_time:                       0.
% 1.89/1.01  
% 1.89/1.01  ------ Problem properties
% 1.89/1.01  
% 1.89/1.01  clauses:                                20
% 1.89/1.01  conjectures:                            0
% 1.89/1.01  epr:                                    0
% 1.89/1.01  horn:                                   18
% 1.89/1.01  ground:                                 5
% 1.89/1.01  unary:                                  5
% 1.89/1.01  binary:                                 10
% 1.89/1.01  lits:                                   43
% 1.89/1.01  lits_eq:                                24
% 1.89/1.01  fd_pure:                                0
% 1.89/1.01  fd_pseudo:                              0
% 1.89/1.01  fd_cond:                                1
% 1.89/1.01  fd_pseudo_cond:                         0
% 1.89/1.01  ac_symbols:                             0
% 1.89/1.01  
% 1.89/1.01  ------ Propositional Solver
% 1.89/1.01  
% 1.89/1.01  prop_solver_calls:                      26
% 1.89/1.01  prop_fast_solver_calls:                 630
% 1.89/1.01  smt_solver_calls:                       0
% 1.89/1.01  smt_fast_solver_calls:                  0
% 1.89/1.01  prop_num_of_clauses:                    974
% 1.89/1.01  prop_preprocess_simplified:             3822
% 1.89/1.01  prop_fo_subsumed:                       10
% 1.89/1.01  prop_solver_time:                       0.
% 1.89/1.01  smt_solver_time:                        0.
% 1.89/1.01  smt_fast_solver_time:                   0.
% 1.89/1.01  prop_fast_solver_time:                  0.
% 1.89/1.01  prop_unsat_core_time:                   0.
% 1.89/1.01  
% 1.89/1.01  ------ QBF
% 1.89/1.01  
% 1.89/1.01  qbf_q_res:                              0
% 1.89/1.01  qbf_num_tautologies:                    0
% 1.89/1.01  qbf_prep_cycles:                        0
% 1.89/1.01  
% 1.89/1.01  ------ BMC1
% 1.89/1.01  
% 1.89/1.01  bmc1_current_bound:                     -1
% 1.89/1.01  bmc1_last_solved_bound:                 -1
% 1.89/1.01  bmc1_unsat_core_size:                   -1
% 1.89/1.01  bmc1_unsat_core_parents_size:           -1
% 1.89/1.01  bmc1_merge_next_fun:                    0
% 1.89/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.89/1.01  
% 1.89/1.01  ------ Instantiation
% 1.89/1.01  
% 1.89/1.01  inst_num_of_clauses:                    339
% 1.89/1.01  inst_num_in_passive:                    152
% 1.89/1.01  inst_num_in_active:                     159
% 1.89/1.01  inst_num_in_unprocessed:                28
% 1.89/1.01  inst_num_of_loops:                      210
% 1.89/1.01  inst_num_of_learning_restarts:          0
% 1.89/1.01  inst_num_moves_active_passive:          49
% 1.89/1.01  inst_lit_activity:                      0
% 1.89/1.01  inst_lit_activity_moves:                0
% 1.89/1.01  inst_num_tautologies:                   0
% 1.89/1.01  inst_num_prop_implied:                  0
% 1.89/1.01  inst_num_existing_simplified:           0
% 1.89/1.01  inst_num_eq_res_simplified:             0
% 1.89/1.01  inst_num_child_elim:                    0
% 1.89/1.01  inst_num_of_dismatching_blockings:      101
% 1.89/1.01  inst_num_of_non_proper_insts:           230
% 1.89/1.01  inst_num_of_duplicates:                 0
% 1.89/1.01  inst_inst_num_from_inst_to_res:         0
% 1.89/1.01  inst_dismatching_checking_time:         0.
% 1.89/1.01  
% 1.89/1.01  ------ Resolution
% 1.89/1.01  
% 1.89/1.01  res_num_of_clauses:                     0
% 1.89/1.01  res_num_in_passive:                     0
% 1.89/1.01  res_num_in_active:                      0
% 1.89/1.01  res_num_of_loops:                       111
% 1.89/1.01  res_forward_subset_subsumed:            18
% 1.89/1.01  res_backward_subset_subsumed:           0
% 1.89/1.01  res_forward_subsumed:                   0
% 1.89/1.01  res_backward_subsumed:                  0
% 1.89/1.01  res_forward_subsumption_resolution:     1
% 1.89/1.01  res_backward_subsumption_resolution:    0
% 1.89/1.01  res_clause_to_clause_subsumption:       88
% 1.89/1.01  res_orphan_elimination:                 0
% 1.89/1.01  res_tautology_del:                      26
% 1.89/1.01  res_num_eq_res_simplified:              0
% 1.89/1.01  res_num_sel_changes:                    0
% 1.89/1.01  res_moves_from_active_to_pass:          0
% 1.89/1.01  
% 1.89/1.01  ------ Superposition
% 1.89/1.01  
% 1.89/1.01  sup_time_total:                         0.
% 1.89/1.01  sup_time_generating:                    0.
% 1.89/1.01  sup_time_sim_full:                      0.
% 1.89/1.01  sup_time_sim_immed:                     0.
% 1.89/1.01  
% 1.89/1.01  sup_num_of_clauses:                     34
% 1.89/1.01  sup_num_in_active:                      22
% 1.89/1.01  sup_num_in_passive:                     12
% 1.89/1.01  sup_num_of_loops:                       40
% 1.89/1.01  sup_fw_superposition:                   17
% 1.89/1.01  sup_bw_superposition:                   18
% 1.89/1.01  sup_immediate_simplified:               17
% 1.89/1.01  sup_given_eliminated:                   0
% 1.89/1.01  comparisons_done:                       0
% 1.89/1.01  comparisons_avoided:                    0
% 1.89/1.01  
% 1.89/1.01  ------ Simplifications
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  sim_fw_subset_subsumed:                 4
% 1.89/1.01  sim_bw_subset_subsumed:                 4
% 1.89/1.01  sim_fw_subsumed:                        1
% 1.89/1.01  sim_bw_subsumed:                        0
% 1.89/1.01  sim_fw_subsumption_res:                 2
% 1.89/1.01  sim_bw_subsumption_res:                 0
% 1.89/1.01  sim_tautology_del:                      0
% 1.89/1.01  sim_eq_tautology_del:                   7
% 1.89/1.01  sim_eq_res_simp:                        1
% 1.89/1.01  sim_fw_demodulated:                     10
% 1.89/1.01  sim_bw_demodulated:                     14
% 1.89/1.01  sim_light_normalised:                   17
% 1.89/1.01  sim_joinable_taut:                      0
% 1.89/1.01  sim_joinable_simp:                      0
% 1.89/1.01  sim_ac_normalised:                      0
% 1.89/1.01  sim_smt_subsumption:                    0
% 1.89/1.01  
%------------------------------------------------------------------------------
