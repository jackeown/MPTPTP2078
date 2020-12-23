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
% DateTime   : Thu Dec  3 12:00:17 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  149 (1134 expanded)
%              Number of clauses        :   96 ( 477 expanded)
%              Number of leaves         :   17 ( 213 expanded)
%              Depth                    :   24
%              Number of atoms          :  438 (4072 expanded)
%              Number of equality atoms :  212 ( 953 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
        | ~ v1_funct_1(sK2) )
      & r1_tarski(k2_relat_1(sK2),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
      | ~ v1_funct_1(sK2) )
    & r1_tarski(k2_relat_1(sK2),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f32])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_908,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_913,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_908,c_4])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1287,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_906])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_365,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK2),X1)
    | ~ r1_tarski(k1_relat_1(sK2),X0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_902,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_21])).

cnf(c_129,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(renaming,[status(thm)],[c_128])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK2) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_129])).

cnf(c_455,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_xboole_0 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_455,c_11])).

cnf(c_900,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1107,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_900])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1110,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1107,c_25])).

cnf(c_1577,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1287,c_1110])).

cnf(c_15,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_129])).

cnf(c_439,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_387,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_388,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_521,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_388])).

cnf(c_554,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(bin_hyper_res,[status(thm)],[c_439,c_521])).

cnf(c_899,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_1682,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1577,c_899])).

cnf(c_61,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_60,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_62,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_2,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_75,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_366,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_368,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_978,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_977,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_913])).

cnf(c_979,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_598,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1062,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK2),X2)
    | X2 != X1
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_1063,plain,
    ( X0 != X1
    | k1_relat_1(sK2) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_1065,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_597,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1055,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_1072,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_596,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1073,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_180])).

cnf(c_228,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_181])).

cnf(c_311,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | X0 != X2
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_228])).

cnf(c_312,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k1_xboole_0 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_333,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_345,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_312,c_333])).

cnf(c_346,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1135,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1147,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_1148,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_1028,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK2),X2)
    | X2 != X1
    | k2_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_1140,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | r1_tarski(k2_relat_1(sK2),X1)
    | X1 != X0
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1265,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | X0 != sK1
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1267,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1266,plain,
    ( X0 != sK1
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_1268,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_xboole_0 != sK1
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_904,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1683,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1577,c_904])).

cnf(c_903,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_347,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1779,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_62,c_347,c_978])).

cnf(c_1780,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1779])).

cnf(c_1785,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1683,c_1780])).

cnf(c_905,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1395,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_905])).

cnf(c_1961,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1785,c_1395])).

cnf(c_1963,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1785,c_521])).

cnf(c_1971,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1963])).

cnf(c_1988,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1961,c_1971])).

cnf(c_2003,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1988])).

cnf(c_2098,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1682,c_20,c_25,c_61,c_62,c_2,c_75,c_368,c_388,c_978,c_979,c_1065,c_1072,c_1073,c_1135,c_1148,c_1267,c_1268,c_1577,c_2003])).

cnf(c_2102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2098,c_1971])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2102,c_1577,c_1268,c_1267,c_1148,c_1135,c_1073,c_1072,c_1065,c_979,c_978,c_388,c_368,c_75,c_2,c_62,c_61,c_25,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:24:57 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.66/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.05  
% 1.66/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.66/1.05  
% 1.66/1.05  ------  iProver source info
% 1.66/1.05  
% 1.66/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.66/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.66/1.05  git: non_committed_changes: false
% 1.66/1.05  git: last_make_outside_of_git: false
% 1.66/1.05  
% 1.66/1.05  ------ 
% 1.66/1.05  
% 1.66/1.05  ------ Input Options
% 1.66/1.05  
% 1.66/1.05  --out_options                           all
% 1.66/1.05  --tptp_safe_out                         true
% 1.66/1.05  --problem_path                          ""
% 1.66/1.05  --include_path                          ""
% 1.66/1.05  --clausifier                            res/vclausify_rel
% 1.66/1.05  --clausifier_options                    --mode clausify
% 1.66/1.05  --stdin                                 false
% 1.66/1.05  --stats_out                             all
% 1.66/1.05  
% 1.66/1.05  ------ General Options
% 1.66/1.05  
% 1.66/1.05  --fof                                   false
% 1.66/1.05  --time_out_real                         305.
% 1.66/1.05  --time_out_virtual                      -1.
% 1.66/1.05  --symbol_type_check                     false
% 1.66/1.05  --clausify_out                          false
% 1.66/1.05  --sig_cnt_out                           false
% 1.66/1.05  --trig_cnt_out                          false
% 1.66/1.05  --trig_cnt_out_tolerance                1.
% 1.66/1.05  --trig_cnt_out_sk_spl                   false
% 1.66/1.05  --abstr_cl_out                          false
% 1.66/1.05  
% 1.66/1.05  ------ Global Options
% 1.66/1.05  
% 1.66/1.05  --schedule                              default
% 1.66/1.05  --add_important_lit                     false
% 1.66/1.05  --prop_solver_per_cl                    1000
% 1.66/1.05  --min_unsat_core                        false
% 1.66/1.05  --soft_assumptions                      false
% 1.66/1.05  --soft_lemma_size                       3
% 1.66/1.05  --prop_impl_unit_size                   0
% 1.66/1.05  --prop_impl_unit                        []
% 1.66/1.05  --share_sel_clauses                     true
% 1.66/1.05  --reset_solvers                         false
% 1.66/1.05  --bc_imp_inh                            [conj_cone]
% 1.66/1.05  --conj_cone_tolerance                   3.
% 1.66/1.05  --extra_neg_conj                        none
% 1.66/1.05  --large_theory_mode                     true
% 1.66/1.05  --prolific_symb_bound                   200
% 1.66/1.05  --lt_threshold                          2000
% 1.66/1.05  --clause_weak_htbl                      true
% 1.66/1.05  --gc_record_bc_elim                     false
% 1.66/1.05  
% 1.66/1.05  ------ Preprocessing Options
% 1.66/1.05  
% 1.66/1.05  --preprocessing_flag                    true
% 1.66/1.05  --time_out_prep_mult                    0.1
% 1.66/1.05  --splitting_mode                        input
% 1.66/1.05  --splitting_grd                         true
% 1.66/1.05  --splitting_cvd                         false
% 1.66/1.05  --splitting_cvd_svl                     false
% 1.66/1.05  --splitting_nvd                         32
% 1.66/1.05  --sub_typing                            true
% 1.66/1.05  --prep_gs_sim                           true
% 1.66/1.05  --prep_unflatten                        true
% 1.66/1.05  --prep_res_sim                          true
% 1.66/1.05  --prep_upred                            true
% 1.66/1.05  --prep_sem_filter                       exhaustive
% 1.66/1.05  --prep_sem_filter_out                   false
% 1.66/1.05  --pred_elim                             true
% 1.66/1.05  --res_sim_input                         true
% 1.66/1.05  --eq_ax_congr_red                       true
% 1.66/1.05  --pure_diseq_elim                       true
% 1.66/1.05  --brand_transform                       false
% 1.66/1.05  --non_eq_to_eq                          false
% 1.66/1.05  --prep_def_merge                        true
% 1.66/1.05  --prep_def_merge_prop_impl              false
% 1.66/1.05  --prep_def_merge_mbd                    true
% 1.66/1.05  --prep_def_merge_tr_red                 false
% 1.66/1.05  --prep_def_merge_tr_cl                  false
% 1.66/1.05  --smt_preprocessing                     true
% 1.66/1.05  --smt_ac_axioms                         fast
% 1.66/1.05  --preprocessed_out                      false
% 1.66/1.05  --preprocessed_stats                    false
% 1.66/1.05  
% 1.66/1.05  ------ Abstraction refinement Options
% 1.66/1.05  
% 1.66/1.05  --abstr_ref                             []
% 1.66/1.05  --abstr_ref_prep                        false
% 1.66/1.05  --abstr_ref_until_sat                   false
% 1.66/1.05  --abstr_ref_sig_restrict                funpre
% 1.66/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.05  --abstr_ref_under                       []
% 1.66/1.05  
% 1.66/1.05  ------ SAT Options
% 1.66/1.05  
% 1.66/1.05  --sat_mode                              false
% 1.66/1.05  --sat_fm_restart_options                ""
% 1.66/1.05  --sat_gr_def                            false
% 1.66/1.05  --sat_epr_types                         true
% 1.66/1.05  --sat_non_cyclic_types                  false
% 1.66/1.05  --sat_finite_models                     false
% 1.66/1.05  --sat_fm_lemmas                         false
% 1.66/1.05  --sat_fm_prep                           false
% 1.66/1.05  --sat_fm_uc_incr                        true
% 1.66/1.05  --sat_out_model                         small
% 1.66/1.05  --sat_out_clauses                       false
% 1.66/1.05  
% 1.66/1.05  ------ QBF Options
% 1.66/1.05  
% 1.66/1.05  --qbf_mode                              false
% 1.66/1.05  --qbf_elim_univ                         false
% 1.66/1.05  --qbf_dom_inst                          none
% 1.66/1.05  --qbf_dom_pre_inst                      false
% 1.66/1.05  --qbf_sk_in                             false
% 1.66/1.05  --qbf_pred_elim                         true
% 1.66/1.05  --qbf_split                             512
% 1.66/1.05  
% 1.66/1.05  ------ BMC1 Options
% 1.66/1.05  
% 1.66/1.05  --bmc1_incremental                      false
% 1.66/1.05  --bmc1_axioms                           reachable_all
% 1.66/1.05  --bmc1_min_bound                        0
% 1.66/1.05  --bmc1_max_bound                        -1
% 1.66/1.05  --bmc1_max_bound_default                -1
% 1.66/1.05  --bmc1_symbol_reachability              true
% 1.66/1.05  --bmc1_property_lemmas                  false
% 1.66/1.05  --bmc1_k_induction                      false
% 1.66/1.05  --bmc1_non_equiv_states                 false
% 1.66/1.05  --bmc1_deadlock                         false
% 1.66/1.05  --bmc1_ucm                              false
% 1.66/1.05  --bmc1_add_unsat_core                   none
% 1.66/1.05  --bmc1_unsat_core_children              false
% 1.66/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.05  --bmc1_out_stat                         full
% 1.66/1.05  --bmc1_ground_init                      false
% 1.66/1.05  --bmc1_pre_inst_next_state              false
% 1.66/1.05  --bmc1_pre_inst_state                   false
% 1.66/1.05  --bmc1_pre_inst_reach_state             false
% 1.66/1.05  --bmc1_out_unsat_core                   false
% 1.66/1.05  --bmc1_aig_witness_out                  false
% 1.66/1.05  --bmc1_verbose                          false
% 1.66/1.05  --bmc1_dump_clauses_tptp                false
% 1.66/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.05  --bmc1_dump_file                        -
% 1.66/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.05  --bmc1_ucm_extend_mode                  1
% 1.66/1.05  --bmc1_ucm_init_mode                    2
% 1.66/1.05  --bmc1_ucm_cone_mode                    none
% 1.66/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.05  --bmc1_ucm_relax_model                  4
% 1.66/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.05  --bmc1_ucm_layered_model                none
% 1.66/1.05  --bmc1_ucm_max_lemma_size               10
% 1.66/1.05  
% 1.66/1.05  ------ AIG Options
% 1.66/1.05  
% 1.66/1.05  --aig_mode                              false
% 1.66/1.05  
% 1.66/1.05  ------ Instantiation Options
% 1.66/1.05  
% 1.66/1.05  --instantiation_flag                    true
% 1.66/1.05  --inst_sos_flag                         false
% 1.66/1.05  --inst_sos_phase                        true
% 1.66/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.05  --inst_lit_sel_side                     num_symb
% 1.66/1.05  --inst_solver_per_active                1400
% 1.66/1.05  --inst_solver_calls_frac                1.
% 1.66/1.05  --inst_passive_queue_type               priority_queues
% 1.66/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.05  --inst_passive_queues_freq              [25;2]
% 1.66/1.05  --inst_dismatching                      true
% 1.66/1.05  --inst_eager_unprocessed_to_passive     true
% 1.66/1.05  --inst_prop_sim_given                   true
% 1.66/1.05  --inst_prop_sim_new                     false
% 1.66/1.05  --inst_subs_new                         false
% 1.66/1.05  --inst_eq_res_simp                      false
% 1.66/1.05  --inst_subs_given                       false
% 1.66/1.05  --inst_orphan_elimination               true
% 1.66/1.05  --inst_learning_loop_flag               true
% 1.66/1.05  --inst_learning_start                   3000
% 1.66/1.05  --inst_learning_factor                  2
% 1.66/1.05  --inst_start_prop_sim_after_learn       3
% 1.66/1.05  --inst_sel_renew                        solver
% 1.66/1.05  --inst_lit_activity_flag                true
% 1.66/1.05  --inst_restr_to_given                   false
% 1.66/1.05  --inst_activity_threshold               500
% 1.66/1.05  --inst_out_proof                        true
% 1.66/1.05  
% 1.66/1.05  ------ Resolution Options
% 1.66/1.05  
% 1.66/1.05  --resolution_flag                       true
% 1.66/1.05  --res_lit_sel                           adaptive
% 1.66/1.05  --res_lit_sel_side                      none
% 1.66/1.05  --res_ordering                          kbo
% 1.66/1.05  --res_to_prop_solver                    active
% 1.66/1.05  --res_prop_simpl_new                    false
% 1.66/1.05  --res_prop_simpl_given                  true
% 1.66/1.05  --res_passive_queue_type                priority_queues
% 1.66/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.05  --res_passive_queues_freq               [15;5]
% 1.66/1.05  --res_forward_subs                      full
% 1.66/1.05  --res_backward_subs                     full
% 1.66/1.05  --res_forward_subs_resolution           true
% 1.66/1.05  --res_backward_subs_resolution          true
% 1.66/1.05  --res_orphan_elimination                true
% 1.66/1.05  --res_time_limit                        2.
% 1.66/1.05  --res_out_proof                         true
% 1.66/1.05  
% 1.66/1.05  ------ Superposition Options
% 1.66/1.05  
% 1.66/1.05  --superposition_flag                    true
% 1.66/1.05  --sup_passive_queue_type                priority_queues
% 1.66/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.05  --demod_completeness_check              fast
% 1.66/1.05  --demod_use_ground                      true
% 1.66/1.05  --sup_to_prop_solver                    passive
% 1.66/1.05  --sup_prop_simpl_new                    true
% 1.66/1.05  --sup_prop_simpl_given                  true
% 1.66/1.05  --sup_fun_splitting                     false
% 1.66/1.05  --sup_smt_interval                      50000
% 1.66/1.05  
% 1.66/1.05  ------ Superposition Simplification Setup
% 1.66/1.05  
% 1.66/1.05  --sup_indices_passive                   []
% 1.66/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.05  --sup_full_bw                           [BwDemod]
% 1.66/1.05  --sup_immed_triv                        [TrivRules]
% 1.66/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.05  --sup_immed_bw_main                     []
% 1.66/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.05  
% 1.66/1.05  ------ Combination Options
% 1.66/1.05  
% 1.66/1.05  --comb_res_mult                         3
% 1.66/1.05  --comb_sup_mult                         2
% 1.66/1.05  --comb_inst_mult                        10
% 1.66/1.05  
% 1.66/1.05  ------ Debug Options
% 1.66/1.05  
% 1.66/1.05  --dbg_backtrace                         false
% 1.66/1.05  --dbg_dump_prop_clauses                 false
% 1.66/1.05  --dbg_dump_prop_clauses_file            -
% 1.66/1.05  --dbg_out_stat                          false
% 1.66/1.05  ------ Parsing...
% 1.66/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.66/1.05  
% 1.66/1.05  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.66/1.05  
% 1.66/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.66/1.05  
% 1.66/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.66/1.05  ------ Proving...
% 1.66/1.05  ------ Problem Properties 
% 1.66/1.05  
% 1.66/1.05  
% 1.66/1.05  clauses                                 13
% 1.66/1.05  conjectures                             1
% 1.66/1.05  EPR                                     1
% 1.66/1.05  Horn                                    13
% 1.66/1.05  unary                                   3
% 1.66/1.05  binary                                  6
% 1.66/1.05  lits                                    30
% 1.66/1.05  lits eq                                 13
% 1.66/1.05  fd_pure                                 0
% 1.66/1.05  fd_pseudo                               0
% 1.66/1.05  fd_cond                                 1
% 1.66/1.05  fd_pseudo_cond                          0
% 1.66/1.05  AC symbols                              0
% 1.66/1.05  
% 1.66/1.05  ------ Schedule dynamic 5 is on 
% 1.66/1.05  
% 1.66/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.66/1.05  
% 1.66/1.05  
% 1.66/1.05  ------ 
% 1.66/1.05  Current options:
% 1.66/1.05  ------ 
% 1.66/1.05  
% 1.66/1.05  ------ Input Options
% 1.66/1.05  
% 1.66/1.05  --out_options                           all
% 1.66/1.05  --tptp_safe_out                         true
% 1.66/1.05  --problem_path                          ""
% 1.66/1.05  --include_path                          ""
% 1.66/1.05  --clausifier                            res/vclausify_rel
% 1.66/1.05  --clausifier_options                    --mode clausify
% 1.66/1.05  --stdin                                 false
% 1.66/1.05  --stats_out                             all
% 1.66/1.05  
% 1.66/1.05  ------ General Options
% 1.66/1.05  
% 1.66/1.05  --fof                                   false
% 1.66/1.05  --time_out_real                         305.
% 1.66/1.05  --time_out_virtual                      -1.
% 1.66/1.05  --symbol_type_check                     false
% 1.66/1.05  --clausify_out                          false
% 1.66/1.05  --sig_cnt_out                           false
% 1.66/1.05  --trig_cnt_out                          false
% 1.66/1.05  --trig_cnt_out_tolerance                1.
% 1.66/1.05  --trig_cnt_out_sk_spl                   false
% 1.66/1.05  --abstr_cl_out                          false
% 1.66/1.05  
% 1.66/1.05  ------ Global Options
% 1.66/1.05  
% 1.66/1.05  --schedule                              default
% 1.66/1.05  --add_important_lit                     false
% 1.66/1.05  --prop_solver_per_cl                    1000
% 1.66/1.05  --min_unsat_core                        false
% 1.66/1.05  --soft_assumptions                      false
% 1.66/1.05  --soft_lemma_size                       3
% 1.66/1.05  --prop_impl_unit_size                   0
% 1.66/1.05  --prop_impl_unit                        []
% 1.66/1.05  --share_sel_clauses                     true
% 1.66/1.05  --reset_solvers                         false
% 1.66/1.05  --bc_imp_inh                            [conj_cone]
% 1.66/1.05  --conj_cone_tolerance                   3.
% 1.66/1.05  --extra_neg_conj                        none
% 1.66/1.05  --large_theory_mode                     true
% 1.66/1.05  --prolific_symb_bound                   200
% 1.66/1.05  --lt_threshold                          2000
% 1.66/1.05  --clause_weak_htbl                      true
% 1.66/1.05  --gc_record_bc_elim                     false
% 1.66/1.05  
% 1.66/1.05  ------ Preprocessing Options
% 1.66/1.05  
% 1.66/1.05  --preprocessing_flag                    true
% 1.66/1.05  --time_out_prep_mult                    0.1
% 1.66/1.05  --splitting_mode                        input
% 1.66/1.05  --splitting_grd                         true
% 1.66/1.05  --splitting_cvd                         false
% 1.66/1.05  --splitting_cvd_svl                     false
% 1.66/1.05  --splitting_nvd                         32
% 1.66/1.05  --sub_typing                            true
% 1.66/1.05  --prep_gs_sim                           true
% 1.66/1.05  --prep_unflatten                        true
% 1.66/1.05  --prep_res_sim                          true
% 1.66/1.05  --prep_upred                            true
% 1.66/1.05  --prep_sem_filter                       exhaustive
% 1.66/1.05  --prep_sem_filter_out                   false
% 1.66/1.05  --pred_elim                             true
% 1.66/1.05  --res_sim_input                         true
% 1.66/1.05  --eq_ax_congr_red                       true
% 1.66/1.05  --pure_diseq_elim                       true
% 1.66/1.05  --brand_transform                       false
% 1.66/1.05  --non_eq_to_eq                          false
% 1.66/1.05  --prep_def_merge                        true
% 1.66/1.05  --prep_def_merge_prop_impl              false
% 1.66/1.05  --prep_def_merge_mbd                    true
% 1.66/1.05  --prep_def_merge_tr_red                 false
% 1.66/1.05  --prep_def_merge_tr_cl                  false
% 1.66/1.05  --smt_preprocessing                     true
% 1.66/1.05  --smt_ac_axioms                         fast
% 1.66/1.05  --preprocessed_out                      false
% 1.66/1.05  --preprocessed_stats                    false
% 1.66/1.05  
% 1.66/1.05  ------ Abstraction refinement Options
% 1.66/1.05  
% 1.66/1.05  --abstr_ref                             []
% 1.66/1.05  --abstr_ref_prep                        false
% 1.66/1.05  --abstr_ref_until_sat                   false
% 1.66/1.05  --abstr_ref_sig_restrict                funpre
% 1.66/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.05  --abstr_ref_under                       []
% 1.66/1.05  
% 1.66/1.05  ------ SAT Options
% 1.66/1.05  
% 1.66/1.05  --sat_mode                              false
% 1.66/1.05  --sat_fm_restart_options                ""
% 1.66/1.05  --sat_gr_def                            false
% 1.66/1.05  --sat_epr_types                         true
% 1.66/1.05  --sat_non_cyclic_types                  false
% 1.66/1.05  --sat_finite_models                     false
% 1.66/1.05  --sat_fm_lemmas                         false
% 1.66/1.05  --sat_fm_prep                           false
% 1.66/1.05  --sat_fm_uc_incr                        true
% 1.66/1.05  --sat_out_model                         small
% 1.66/1.05  --sat_out_clauses                       false
% 1.66/1.05  
% 1.66/1.05  ------ QBF Options
% 1.66/1.05  
% 1.66/1.05  --qbf_mode                              false
% 1.66/1.05  --qbf_elim_univ                         false
% 1.66/1.05  --qbf_dom_inst                          none
% 1.66/1.05  --qbf_dom_pre_inst                      false
% 1.66/1.05  --qbf_sk_in                             false
% 1.66/1.05  --qbf_pred_elim                         true
% 1.66/1.05  --qbf_split                             512
% 1.66/1.05  
% 1.66/1.05  ------ BMC1 Options
% 1.66/1.05  
% 1.66/1.05  --bmc1_incremental                      false
% 1.66/1.05  --bmc1_axioms                           reachable_all
% 1.66/1.05  --bmc1_min_bound                        0
% 1.66/1.05  --bmc1_max_bound                        -1
% 1.66/1.05  --bmc1_max_bound_default                -1
% 1.66/1.05  --bmc1_symbol_reachability              true
% 1.66/1.05  --bmc1_property_lemmas                  false
% 1.66/1.05  --bmc1_k_induction                      false
% 1.66/1.05  --bmc1_non_equiv_states                 false
% 1.66/1.05  --bmc1_deadlock                         false
% 1.66/1.05  --bmc1_ucm                              false
% 1.66/1.05  --bmc1_add_unsat_core                   none
% 1.66/1.05  --bmc1_unsat_core_children              false
% 1.66/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.05  --bmc1_out_stat                         full
% 1.66/1.05  --bmc1_ground_init                      false
% 1.66/1.05  --bmc1_pre_inst_next_state              false
% 1.66/1.05  --bmc1_pre_inst_state                   false
% 1.66/1.05  --bmc1_pre_inst_reach_state             false
% 1.66/1.05  --bmc1_out_unsat_core                   false
% 1.66/1.05  --bmc1_aig_witness_out                  false
% 1.66/1.05  --bmc1_verbose                          false
% 1.66/1.05  --bmc1_dump_clauses_tptp                false
% 1.66/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.05  --bmc1_dump_file                        -
% 1.66/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.05  --bmc1_ucm_extend_mode                  1
% 1.66/1.05  --bmc1_ucm_init_mode                    2
% 1.66/1.05  --bmc1_ucm_cone_mode                    none
% 1.66/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.05  --bmc1_ucm_relax_model                  4
% 1.66/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.05  --bmc1_ucm_layered_model                none
% 1.66/1.05  --bmc1_ucm_max_lemma_size               10
% 1.66/1.05  
% 1.66/1.05  ------ AIG Options
% 1.66/1.05  
% 1.66/1.05  --aig_mode                              false
% 1.66/1.05  
% 1.66/1.05  ------ Instantiation Options
% 1.66/1.05  
% 1.66/1.05  --instantiation_flag                    true
% 1.66/1.05  --inst_sos_flag                         false
% 1.66/1.05  --inst_sos_phase                        true
% 1.66/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.05  --inst_lit_sel_side                     none
% 1.66/1.05  --inst_solver_per_active                1400
% 1.66/1.05  --inst_solver_calls_frac                1.
% 1.66/1.05  --inst_passive_queue_type               priority_queues
% 1.66/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.05  --inst_passive_queues_freq              [25;2]
% 1.66/1.05  --inst_dismatching                      true
% 1.66/1.05  --inst_eager_unprocessed_to_passive     true
% 1.66/1.05  --inst_prop_sim_given                   true
% 1.66/1.05  --inst_prop_sim_new                     false
% 1.66/1.05  --inst_subs_new                         false
% 1.66/1.05  --inst_eq_res_simp                      false
% 1.66/1.05  --inst_subs_given                       false
% 1.66/1.05  --inst_orphan_elimination               true
% 1.66/1.05  --inst_learning_loop_flag               true
% 1.66/1.05  --inst_learning_start                   3000
% 1.66/1.05  --inst_learning_factor                  2
% 1.66/1.05  --inst_start_prop_sim_after_learn       3
% 1.66/1.05  --inst_sel_renew                        solver
% 1.66/1.05  --inst_lit_activity_flag                true
% 1.66/1.05  --inst_restr_to_given                   false
% 1.66/1.05  --inst_activity_threshold               500
% 1.66/1.05  --inst_out_proof                        true
% 1.66/1.05  
% 1.66/1.05  ------ Resolution Options
% 1.66/1.05  
% 1.66/1.05  --resolution_flag                       false
% 1.66/1.05  --res_lit_sel                           adaptive
% 1.66/1.05  --res_lit_sel_side                      none
% 1.66/1.05  --res_ordering                          kbo
% 1.66/1.05  --res_to_prop_solver                    active
% 1.66/1.05  --res_prop_simpl_new                    false
% 1.66/1.05  --res_prop_simpl_given                  true
% 1.66/1.05  --res_passive_queue_type                priority_queues
% 1.66/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.05  --res_passive_queues_freq               [15;5]
% 1.66/1.05  --res_forward_subs                      full
% 1.66/1.05  --res_backward_subs                     full
% 1.66/1.05  --res_forward_subs_resolution           true
% 1.66/1.05  --res_backward_subs_resolution          true
% 1.66/1.05  --res_orphan_elimination                true
% 1.66/1.05  --res_time_limit                        2.
% 1.66/1.05  --res_out_proof                         true
% 1.66/1.05  
% 1.66/1.05  ------ Superposition Options
% 1.66/1.05  
% 1.66/1.05  --superposition_flag                    true
% 1.66/1.05  --sup_passive_queue_type                priority_queues
% 1.66/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.05  --demod_completeness_check              fast
% 1.66/1.05  --demod_use_ground                      true
% 1.66/1.05  --sup_to_prop_solver                    passive
% 1.66/1.05  --sup_prop_simpl_new                    true
% 1.66/1.05  --sup_prop_simpl_given                  true
% 1.66/1.05  --sup_fun_splitting                     false
% 1.66/1.05  --sup_smt_interval                      50000
% 1.66/1.05  
% 1.66/1.05  ------ Superposition Simplification Setup
% 1.66/1.05  
% 1.66/1.05  --sup_indices_passive                   []
% 1.66/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.05  --sup_full_bw                           [BwDemod]
% 1.66/1.05  --sup_immed_triv                        [TrivRules]
% 1.66/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.05  --sup_immed_bw_main                     []
% 1.66/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.05  
% 1.66/1.05  ------ Combination Options
% 1.66/1.05  
% 1.66/1.05  --comb_res_mult                         3
% 1.66/1.05  --comb_sup_mult                         2
% 1.66/1.05  --comb_inst_mult                        10
% 1.66/1.05  
% 1.66/1.05  ------ Debug Options
% 1.66/1.05  
% 1.66/1.05  --dbg_backtrace                         false
% 1.66/1.05  --dbg_dump_prop_clauses                 false
% 1.66/1.05  --dbg_dump_prop_clauses_file            -
% 1.66/1.05  --dbg_out_stat                          false
% 1.66/1.05  
% 1.66/1.05  
% 1.66/1.05  
% 1.66/1.05  
% 1.66/1.05  ------ Proving...
% 1.66/1.05  
% 1.66/1.05  
% 1.66/1.05  % SZS status Theorem for theBenchmark.p
% 1.66/1.05  
% 1.66/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.66/1.05  
% 1.66/1.05  fof(f5,axiom,(
% 1.66/1.05    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.66/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.05  
% 1.66/1.05  fof(f39,plain,(
% 1.66/1.05    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.66/1.05    inference(cnf_transformation,[],[f5])).
% 1.66/1.05  
% 1.66/1.05  fof(f4,axiom,(
% 1.66/1.05    ! [X0] : k2_subset_1(X0) = X0),
% 1.66/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.05  
% 1.66/1.05  fof(f38,plain,(
% 1.66/1.05    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.66/1.05    inference(cnf_transformation,[],[f4])).
% 1.66/1.05  
% 1.66/1.05  fof(f6,axiom,(
% 1.66/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.05  
% 1.66/1.05  fof(f29,plain,(
% 1.66/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.66/1.05    inference(nnf_transformation,[],[f6])).
% 1.66/1.05  
% 1.66/1.05  fof(f40,plain,(
% 1.66/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.66/1.05    inference(cnf_transformation,[],[f29])).
% 1.66/1.05  
% 1.66/1.05  fof(f10,axiom,(
% 1.66/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f21,plain,(
% 1.66/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.66/1.06    inference(ennf_transformation,[],[f10])).
% 1.66/1.06  
% 1.66/1.06  fof(f22,plain,(
% 1.66/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.66/1.06    inference(flattening,[],[f21])).
% 1.66/1.06  
% 1.66/1.06  fof(f46,plain,(
% 1.66/1.06    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.66/1.06    inference(cnf_transformation,[],[f22])).
% 1.66/1.06  
% 1.66/1.06  fof(f12,conjecture,(
% 1.66/1.06    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f13,negated_conjecture,(
% 1.66/1.06    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.66/1.06    inference(negated_conjecture,[],[f12])).
% 1.66/1.06  
% 1.66/1.06  fof(f25,plain,(
% 1.66/1.06    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.66/1.06    inference(ennf_transformation,[],[f13])).
% 1.66/1.06  
% 1.66/1.06  fof(f26,plain,(
% 1.66/1.06    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.66/1.06    inference(flattening,[],[f25])).
% 1.66/1.06  
% 1.66/1.06  fof(f32,plain,(
% 1.66/1.06    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.66/1.06    introduced(choice_axiom,[])).
% 1.66/1.06  
% 1.66/1.06  fof(f33,plain,(
% 1.66/1.06    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.66/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f32])).
% 1.66/1.06  
% 1.66/1.06  fof(f53,plain,(
% 1.66/1.06    v1_relat_1(sK2)),
% 1.66/1.06    inference(cnf_transformation,[],[f33])).
% 1.66/1.06  
% 1.66/1.06  fof(f11,axiom,(
% 1.66/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f23,plain,(
% 1.66/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/1.06    inference(ennf_transformation,[],[f11])).
% 1.66/1.06  
% 1.66/1.06  fof(f24,plain,(
% 1.66/1.06    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/1.06    inference(flattening,[],[f23])).
% 1.66/1.06  
% 1.66/1.06  fof(f31,plain,(
% 1.66/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/1.06    inference(nnf_transformation,[],[f24])).
% 1.66/1.06  
% 1.66/1.06  fof(f49,plain,(
% 1.66/1.06    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/1.06    inference(cnf_transformation,[],[f31])).
% 1.66/1.06  
% 1.66/1.06  fof(f56,plain,(
% 1.66/1.06    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)),
% 1.66/1.06    inference(cnf_transformation,[],[f33])).
% 1.66/1.06  
% 1.66/1.06  fof(f54,plain,(
% 1.66/1.06    v1_funct_1(sK2)),
% 1.66/1.06    inference(cnf_transformation,[],[f33])).
% 1.66/1.06  
% 1.66/1.06  fof(f9,axiom,(
% 1.66/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f20,plain,(
% 1.66/1.06    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/1.06    inference(ennf_transformation,[],[f9])).
% 1.66/1.06  
% 1.66/1.06  fof(f45,plain,(
% 1.66/1.06    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/1.06    inference(cnf_transformation,[],[f20])).
% 1.66/1.06  
% 1.66/1.06  fof(f55,plain,(
% 1.66/1.06    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.66/1.06    inference(cnf_transformation,[],[f33])).
% 1.66/1.06  
% 1.66/1.06  fof(f50,plain,(
% 1.66/1.06    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/1.06    inference(cnf_transformation,[],[f31])).
% 1.66/1.06  
% 1.66/1.06  fof(f61,plain,(
% 1.66/1.06    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.66/1.06    inference(equality_resolution,[],[f50])).
% 1.66/1.06  
% 1.66/1.06  fof(f8,axiom,(
% 1.66/1.06    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f19,plain,(
% 1.66/1.06    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.66/1.06    inference(ennf_transformation,[],[f8])).
% 1.66/1.06  
% 1.66/1.06  fof(f30,plain,(
% 1.66/1.06    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.66/1.06    inference(nnf_transformation,[],[f19])).
% 1.66/1.06  
% 1.66/1.06  fof(f44,plain,(
% 1.66/1.06    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.66/1.06    inference(cnf_transformation,[],[f30])).
% 1.66/1.06  
% 1.66/1.06  fof(f2,axiom,(
% 1.66/1.06    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f15,plain,(
% 1.66/1.06    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.66/1.06    inference(ennf_transformation,[],[f2])).
% 1.66/1.06  
% 1.66/1.06  fof(f35,plain,(
% 1.66/1.06    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.66/1.06    inference(cnf_transformation,[],[f15])).
% 1.66/1.06  
% 1.66/1.06  fof(f57,plain,(
% 1.66/1.06    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.66/1.06    inference(equality_resolution,[],[f35])).
% 1.66/1.06  
% 1.66/1.06  fof(f36,plain,(
% 1.66/1.06    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.66/1.06    inference(cnf_transformation,[],[f15])).
% 1.66/1.06  
% 1.66/1.06  fof(f1,axiom,(
% 1.66/1.06    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f14,plain,(
% 1.66/1.06    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.66/1.06    inference(ennf_transformation,[],[f1])).
% 1.66/1.06  
% 1.66/1.06  fof(f27,plain,(
% 1.66/1.06    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.66/1.06    introduced(choice_axiom,[])).
% 1.66/1.06  
% 1.66/1.06  fof(f28,plain,(
% 1.66/1.06    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.66/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 1.66/1.06  
% 1.66/1.06  fof(f34,plain,(
% 1.66/1.06    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.66/1.06    inference(cnf_transformation,[],[f28])).
% 1.66/1.06  
% 1.66/1.06  fof(f7,axiom,(
% 1.66/1.06    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f18,plain,(
% 1.66/1.06    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.66/1.06    inference(ennf_transformation,[],[f7])).
% 1.66/1.06  
% 1.66/1.06  fof(f42,plain,(
% 1.66/1.06    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.66/1.06    inference(cnf_transformation,[],[f18])).
% 1.66/1.06  
% 1.66/1.06  fof(f41,plain,(
% 1.66/1.06    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.66/1.06    inference(cnf_transformation,[],[f29])).
% 1.66/1.06  
% 1.66/1.06  fof(f3,axiom,(
% 1.66/1.06    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.66/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.06  
% 1.66/1.06  fof(f16,plain,(
% 1.66/1.06    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.66/1.06    inference(ennf_transformation,[],[f3])).
% 1.66/1.06  
% 1.66/1.06  fof(f17,plain,(
% 1.66/1.06    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.66/1.06    inference(flattening,[],[f16])).
% 1.66/1.06  
% 1.66/1.06  fof(f37,plain,(
% 1.66/1.06    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.66/1.06    inference(cnf_transformation,[],[f17])).
% 1.66/1.06  
% 1.66/1.06  cnf(c_5,plain,
% 1.66/1.06      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.66/1.06      inference(cnf_transformation,[],[f39]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_908,plain,
% 1.66/1.06      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_4,plain,
% 1.66/1.06      ( k2_subset_1(X0) = X0 ),
% 1.66/1.06      inference(cnf_transformation,[],[f38]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_913,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.66/1.06      inference(light_normalisation,[status(thm)],[c_908,c_4]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_7,plain,
% 1.66/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.66/1.06      inference(cnf_transformation,[],[f40]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_906,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.66/1.06      | r1_tarski(X0,X1) = iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1287,plain,
% 1.66/1.06      ( r1_tarski(X0,X0) = iProver_top ),
% 1.66/1.06      inference(superposition,[status(thm)],[c_913,c_906]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_12,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/1.06      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.66/1.06      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.66/1.06      | ~ v1_relat_1(X0) ),
% 1.66/1.06      inference(cnf_transformation,[],[f46]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_22,negated_conjecture,
% 1.66/1.06      ( v1_relat_1(sK2) ),
% 1.66/1.06      inference(cnf_transformation,[],[f53]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_364,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/1.06      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.66/1.06      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.66/1.06      | sK2 != X0 ),
% 1.66/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_365,plain,
% 1.66/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.66/1.06      | ~ r1_tarski(k2_relat_1(sK2),X1)
% 1.66/1.06      | ~ r1_tarski(k1_relat_1(sK2),X0) ),
% 1.66/1.06      inference(unflattening,[status(thm)],[c_364]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_902,plain,
% 1.66/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_16,plain,
% 1.66/1.06      ( v1_funct_2(X0,X1,X2)
% 1.66/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/1.06      | k1_relset_1(X1,X2,X0) != X1
% 1.66/1.06      | k1_xboole_0 = X2 ),
% 1.66/1.06      inference(cnf_transformation,[],[f49]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_19,negated_conjecture,
% 1.66/1.06      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 1.66/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | ~ v1_funct_1(sK2) ),
% 1.66/1.06      inference(cnf_transformation,[],[f56]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_21,negated_conjecture,
% 1.66/1.06      ( v1_funct_1(sK2) ),
% 1.66/1.06      inference(cnf_transformation,[],[f54]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_128,plain,
% 1.66/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
% 1.66/1.06      inference(global_propositional_subsumption,
% 1.66/1.06                [status(thm)],
% 1.66/1.06                [c_19,c_21]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_129,negated_conjecture,
% 1.66/1.06      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 1.66/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
% 1.66/1.06      inference(renaming,[status(thm)],[c_128]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_454,plain,
% 1.66/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | k1_relset_1(X1,X2,X0) != X1
% 1.66/1.06      | k1_relat_1(sK2) != X1
% 1.66/1.06      | sK1 != X2
% 1.66/1.06      | sK2 != X0
% 1.66/1.06      | k1_xboole_0 = X2 ),
% 1.66/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_129]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_455,plain,
% 1.66/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
% 1.66/1.06      | k1_xboole_0 = sK1 ),
% 1.66/1.06      inference(unflattening,[status(thm)],[c_454]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_11,plain,
% 1.66/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/1.06      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.66/1.06      inference(cnf_transformation,[],[f45]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_463,plain,
% 1.66/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | k1_xboole_0 = sK1 ),
% 1.66/1.06      inference(forward_subsumption_resolution,
% 1.66/1.06                [status(thm)],
% 1.66/1.06                [c_455,c_11]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_900,plain,
% 1.66/1.06      ( k1_xboole_0 = sK1
% 1.66/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1107,plain,
% 1.66/1.06      ( sK1 = k1_xboole_0
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 1.66/1.06      inference(superposition,[status(thm)],[c_902,c_900]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_20,negated_conjecture,
% 1.66/1.06      ( r1_tarski(k2_relat_1(sK2),sK1) ),
% 1.66/1.06      inference(cnf_transformation,[],[f55]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_25,plain,
% 1.66/1.06      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1110,plain,
% 1.66/1.06      ( sK1 = k1_xboole_0
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 1.66/1.06      inference(global_propositional_subsumption,
% 1.66/1.06                [status(thm)],
% 1.66/1.06                [c_1107,c_25]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1577,plain,
% 1.66/1.06      ( sK1 = k1_xboole_0 ),
% 1.66/1.06      inference(superposition,[status(thm)],[c_1287,c_1110]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_15,plain,
% 1.66/1.06      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.66/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.66/1.06      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.66/1.06      inference(cnf_transformation,[],[f61]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_438,plain,
% 1.66/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.66/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.66/1.06      | k1_relat_1(sK2) != k1_xboole_0
% 1.66/1.06      | sK1 != X1
% 1.66/1.06      | sK2 != X0 ),
% 1.66/1.06      inference(resolution_lifted,[status(thm)],[c_15,c_129]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_439,plain,
% 1.66/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 1.66/1.06      | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 1.66/1.06      | k1_relat_1(sK2) != k1_xboole_0 ),
% 1.66/1.06      inference(unflattening,[status(thm)],[c_438]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_9,plain,
% 1.66/1.06      ( ~ v1_relat_1(X0)
% 1.66/1.06      | k2_relat_1(X0) != k1_xboole_0
% 1.66/1.06      | k1_relat_1(X0) = k1_xboole_0 ),
% 1.66/1.06      inference(cnf_transformation,[],[f44]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_387,plain,
% 1.66/1.06      ( k2_relat_1(X0) != k1_xboole_0
% 1.66/1.06      | k1_relat_1(X0) = k1_xboole_0
% 1.66/1.06      | sK2 != X0 ),
% 1.66/1.06      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_388,plain,
% 1.66/1.06      ( k2_relat_1(sK2) != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.66/1.06      inference(unflattening,[status(thm)],[c_387]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_521,plain,
% 1.66/1.06      ( k2_relat_1(sK2) != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.66/1.06      inference(prop_impl,[status(thm)],[c_388]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_554,plain,
% 1.66/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.66/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 1.66/1.06      | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 1.66/1.06      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.66/1.06      inference(bin_hyper_res,[status(thm)],[c_439,c_521]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_899,plain,
% 1.66/1.06      ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 1.66/1.06      | k2_relat_1(sK2) != k1_xboole_0
% 1.66/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top
% 1.66/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1682,plain,
% 1.66/1.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
% 1.66/1.06      | k2_relat_1(sK2) != k1_xboole_0
% 1.66/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 1.66/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.66/1.06      inference(demodulation,[status(thm)],[c_1577,c_899]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_61,plain,
% 1.66/1.06      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 1.66/1.06      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_7]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_60,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.66/1.06      | r1_tarski(X0,X1) = iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_62,plain,
% 1.66/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.66/1.06      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_60]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_2,plain,
% 1.66/1.06      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.66/1.06      inference(cnf_transformation,[],[f57]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1,plain,
% 1.66/1.06      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 1.66/1.06      inference(cnf_transformation,[],[f36]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_75,plain,
% 1.66/1.06      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.66/1.06      | k1_xboole_0 = k1_xboole_0 ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_366,plain,
% 1.66/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_368,plain,
% 1.66/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_366]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_978,plain,
% 1.66/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_913]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_977,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 1.66/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_913]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_979,plain,
% 1.66/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_977]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_598,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.66/1.06      theory(equality) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1062,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1)
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),X2)
% 1.66/1.06      | X2 != X1
% 1.66/1.06      | k1_relat_1(sK2) != X0 ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_598]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1063,plain,
% 1.66/1.06      ( X0 != X1
% 1.66/1.06      | k1_relat_1(sK2) != X2
% 1.66/1.06      | r1_tarski(X2,X1) != iProver_top
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),X0) = iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1065,plain,
% 1.66/1.06      ( k1_relat_1(sK2) != k1_xboole_0
% 1.66/1.06      | k1_xboole_0 != k1_xboole_0
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top
% 1.66/1.06      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1063]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_597,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1055,plain,
% 1.66/1.06      ( k2_relat_1(sK2) != X0
% 1.66/1.06      | k2_relat_1(sK2) = k1_xboole_0
% 1.66/1.06      | k1_xboole_0 != X0 ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_597]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1072,plain,
% 1.66/1.06      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 1.66/1.06      | k2_relat_1(sK2) = k1_xboole_0
% 1.66/1.06      | k1_xboole_0 != k2_relat_1(sK2) ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1055]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_596,plain,( X0 = X0 ),theory(equality) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1073,plain,
% 1.66/1.06      ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_596]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_0,plain,
% 1.66/1.06      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.66/1.06      inference(cnf_transformation,[],[f34]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_8,plain,
% 1.66/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.66/1.06      | ~ r2_hidden(X2,X0)
% 1.66/1.06      | ~ v1_xboole_0(X1) ),
% 1.66/1.06      inference(cnf_transformation,[],[f42]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_6,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.66/1.06      inference(cnf_transformation,[],[f41]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_180,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.66/1.06      inference(prop_impl,[status(thm)],[c_6]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_181,plain,
% 1.66/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.66/1.06      inference(renaming,[status(thm)],[c_180]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_228,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 1.66/1.06      inference(bin_hyper_res,[status(thm)],[c_8,c_181]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_311,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1)
% 1.66/1.06      | ~ v1_xboole_0(X1)
% 1.66/1.06      | X0 != X2
% 1.66/1.06      | sK0(X2) != X3
% 1.66/1.06      | k1_xboole_0 = X2 ),
% 1.66/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_228]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_312,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | k1_xboole_0 = X0 ),
% 1.66/1.06      inference(unflattening,[status(thm)],[c_311]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_3,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 1.66/1.06      inference(cnf_transformation,[],[f37]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_332,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1)
% 1.66/1.06      | v1_xboole_0(X0)
% 1.66/1.06      | k1_xboole_0 != X1
% 1.66/1.06      | k1_xboole_0 != X0 ),
% 1.66/1.06      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_333,plain,
% 1.66/1.06      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) ),
% 1.66/1.06      inference(unflattening,[status(thm)],[c_332]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_345,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1)
% 1.66/1.06      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.66/1.06      | k1_xboole_0 != X1
% 1.66/1.06      | k1_xboole_0 = X0 ),
% 1.66/1.06      inference(resolution_lifted,[status(thm)],[c_312,c_333]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_346,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,k1_xboole_0)
% 1.66/1.06      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.66/1.06      | k1_xboole_0 = X0 ),
% 1.66/1.06      inference(unflattening,[status(thm)],[c_345]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1135,plain,
% 1.66/1.06      ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
% 1.66/1.06      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.66/1.06      | k1_xboole_0 = k2_relat_1(sK2) ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_346]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1147,plain,
% 1.66/1.06      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_597]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1148,plain,
% 1.66/1.06      ( sK1 != k1_xboole_0
% 1.66/1.06      | k1_xboole_0 = sK1
% 1.66/1.06      | k1_xboole_0 != k1_xboole_0 ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1147]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1028,plain,
% 1.66/1.06      ( ~ r1_tarski(X0,X1)
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),X2)
% 1.66/1.06      | X2 != X1
% 1.66/1.06      | k2_relat_1(sK2) != X0 ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_598]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1140,plain,
% 1.66/1.06      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),X1)
% 1.66/1.06      | X1 != X0
% 1.66/1.06      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1028]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1265,plain,
% 1.66/1.06      ( r1_tarski(k2_relat_1(sK2),X0)
% 1.66/1.06      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 1.66/1.06      | X0 != sK1
% 1.66/1.06      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1140]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1267,plain,
% 1.66/1.06      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),k1_xboole_0)
% 1.66/1.06      | k2_relat_1(sK2) != k2_relat_1(sK2)
% 1.66/1.06      | k1_xboole_0 != sK1 ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1265]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1266,plain,
% 1.66/1.06      ( X0 != sK1
% 1.66/1.06      | k2_relat_1(sK2) != k2_relat_1(sK2)
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),X0) = iProver_top
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1268,plain,
% 1.66/1.06      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 1.66/1.06      | k1_xboole_0 != sK1
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1266]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_904,plain,
% 1.66/1.06      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1683,plain,
% 1.66/1.06      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 1.66/1.06      inference(demodulation,[status(thm)],[c_1577,c_904]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_903,plain,
% 1.66/1.06      ( k1_xboole_0 = X0
% 1.66/1.06      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 1.66/1.06      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_347,plain,
% 1.66/1.06      ( k1_xboole_0 = X0
% 1.66/1.06      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 1.66/1.06      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1779,plain,
% 1.66/1.06      ( r1_tarski(X0,k1_xboole_0) != iProver_top | k1_xboole_0 = X0 ),
% 1.66/1.06      inference(global_propositional_subsumption,
% 1.66/1.06                [status(thm)],
% 1.66/1.06                [c_903,c_62,c_347,c_978]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1780,plain,
% 1.66/1.06      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.66/1.06      inference(renaming,[status(thm)],[c_1779]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1785,plain,
% 1.66/1.06      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 1.66/1.06      inference(superposition,[status(thm)],[c_1683,c_1780]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_905,plain,
% 1.66/1.06      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.66/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.66/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1395,plain,
% 1.66/1.06      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.66/1.06      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 1.66/1.06      inference(superposition,[status(thm)],[c_902,c_905]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1961,plain,
% 1.66/1.06      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.66/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 1.66/1.06      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 1.66/1.06      inference(demodulation,[status(thm)],[c_1785,c_1395]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1963,plain,
% 1.66/1.06      ( k1_relat_1(sK2) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.66/1.06      inference(demodulation,[status(thm)],[c_1785,c_521]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1971,plain,
% 1.66/1.06      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 1.66/1.06      inference(equality_resolution_simp,[status(thm)],[c_1963]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_1988,plain,
% 1.66/1.06      ( k1_relset_1(X0,X1,sK2) = k1_xboole_0
% 1.66/1.06      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 1.66/1.06      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 1.66/1.06      inference(light_normalisation,[status(thm)],[c_1961,c_1971]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_2003,plain,
% 1.66/1.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
% 1.66/1.06      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.66/1.06      inference(instantiation,[status(thm)],[c_1988]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_2098,plain,
% 1.66/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 1.66/1.06      inference(global_propositional_subsumption,
% 1.66/1.06                [status(thm)],
% 1.66/1.06                [c_1682,c_20,c_25,c_61,c_62,c_2,c_75,c_368,c_388,c_978,
% 1.66/1.06                 c_979,c_1065,c_1072,c_1073,c_1135,c_1148,c_1267,c_1268,
% 1.66/1.06                 c_1577,c_2003]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(c_2102,plain,
% 1.66/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.66/1.06      inference(light_normalisation,[status(thm)],[c_2098,c_1971]) ).
% 1.66/1.06  
% 1.66/1.06  cnf(contradiction,plain,
% 1.66/1.06      ( $false ),
% 1.66/1.06      inference(minisat,
% 1.66/1.06                [status(thm)],
% 1.66/1.06                [c_2102,c_1577,c_1268,c_1267,c_1148,c_1135,c_1073,c_1072,
% 1.66/1.06                 c_1065,c_979,c_978,c_388,c_368,c_75,c_2,c_62,c_61,c_25,
% 1.66/1.06                 c_20]) ).
% 1.66/1.06  
% 1.66/1.06  
% 1.66/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.66/1.06  
% 1.66/1.06  ------                               Statistics
% 1.66/1.06  
% 1.66/1.06  ------ General
% 1.66/1.06  
% 1.66/1.06  abstr_ref_over_cycles:                  0
% 1.66/1.06  abstr_ref_under_cycles:                 0
% 1.66/1.06  gc_basic_clause_elim:                   0
% 1.66/1.06  forced_gc_time:                         0
% 1.66/1.06  parsing_time:                           0.019
% 1.66/1.06  unif_index_cands_time:                  0.
% 1.66/1.06  unif_index_add_time:                    0.
% 1.66/1.06  orderings_time:                         0.
% 1.66/1.06  out_proof_time:                         0.013
% 1.66/1.06  total_time:                             0.096
% 1.66/1.06  num_of_symbols:                         49
% 1.66/1.06  num_of_terms:                           1603
% 1.66/1.06  
% 1.66/1.06  ------ Preprocessing
% 1.66/1.06  
% 1.66/1.06  num_of_splits:                          0
% 1.66/1.06  num_of_split_atoms:                     0
% 1.66/1.06  num_of_reused_defs:                     0
% 1.66/1.06  num_eq_ax_congr_red:                    8
% 1.66/1.06  num_of_sem_filtered_clauses:            2
% 1.66/1.06  num_of_subtypes:                        0
% 1.66/1.06  monotx_restored_types:                  0
% 1.66/1.06  sat_num_of_epr_types:                   0
% 1.66/1.06  sat_num_of_non_cyclic_types:            0
% 1.66/1.06  sat_guarded_non_collapsed_types:        0
% 1.66/1.06  num_pure_diseq_elim:                    0
% 1.66/1.06  simp_replaced_by:                       0
% 1.66/1.06  res_preprocessed:                       81
% 1.66/1.06  prep_upred:                             0
% 1.66/1.06  prep_unflattend:                        35
% 1.66/1.06  smt_new_axioms:                         0
% 1.66/1.06  pred_elim_cands:                        2
% 1.66/1.06  pred_elim:                              5
% 1.66/1.06  pred_elim_cl:                           9
% 1.66/1.06  pred_elim_cycles:                       7
% 1.66/1.06  merged_defs:                            14
% 1.66/1.06  merged_defs_ncl:                        0
% 1.66/1.06  bin_hyper_res:                          16
% 1.66/1.06  prep_cycles:                            4
% 1.66/1.06  pred_elim_time:                         0.004
% 1.66/1.06  splitting_time:                         0.
% 1.66/1.06  sem_filter_time:                        0.
% 1.66/1.06  monotx_time:                            0.001
% 1.66/1.06  subtype_inf_time:                       0.
% 1.66/1.06  
% 1.66/1.06  ------ Problem properties
% 1.66/1.06  
% 1.66/1.06  clauses:                                13
% 1.66/1.06  conjectures:                            1
% 1.66/1.06  epr:                                    1
% 1.66/1.06  horn:                                   13
% 1.66/1.06  ground:                                 6
% 1.66/1.06  unary:                                  3
% 1.66/1.06  binary:                                 6
% 1.66/1.06  lits:                                   30
% 1.66/1.06  lits_eq:                                13
% 1.66/1.06  fd_pure:                                0
% 1.66/1.06  fd_pseudo:                              0
% 1.66/1.06  fd_cond:                                1
% 1.66/1.06  fd_pseudo_cond:                         0
% 1.66/1.06  ac_symbols:                             0
% 1.66/1.06  
% 1.66/1.06  ------ Propositional Solver
% 1.66/1.06  
% 1.66/1.06  prop_solver_calls:                      28
% 1.66/1.06  prop_fast_solver_calls:                 484
% 1.66/1.06  smt_solver_calls:                       0
% 1.66/1.06  smt_fast_solver_calls:                  0
% 1.66/1.06  prop_num_of_clauses:                    677
% 1.66/1.06  prop_preprocess_simplified:             2707
% 1.66/1.06  prop_fo_subsumed:                       6
% 1.66/1.06  prop_solver_time:                       0.
% 1.66/1.06  smt_solver_time:                        0.
% 1.66/1.06  smt_fast_solver_time:                   0.
% 1.66/1.06  prop_fast_solver_time:                  0.
% 1.66/1.06  prop_unsat_core_time:                   0.
% 1.66/1.06  
% 1.66/1.06  ------ QBF
% 1.66/1.06  
% 1.66/1.06  qbf_q_res:                              0
% 1.66/1.06  qbf_num_tautologies:                    0
% 1.66/1.06  qbf_prep_cycles:                        0
% 1.66/1.06  
% 1.66/1.06  ------ BMC1
% 1.66/1.06  
% 1.66/1.06  bmc1_current_bound:                     -1
% 1.66/1.06  bmc1_last_solved_bound:                 -1
% 1.66/1.06  bmc1_unsat_core_size:                   -1
% 1.66/1.06  bmc1_unsat_core_parents_size:           -1
% 1.66/1.06  bmc1_merge_next_fun:                    0
% 1.66/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.66/1.06  
% 1.66/1.06  ------ Instantiation
% 1.66/1.06  
% 1.66/1.06  inst_num_of_clauses:                    216
% 1.66/1.06  inst_num_in_passive:                    94
% 1.66/1.06  inst_num_in_active:                     104
% 1.66/1.06  inst_num_in_unprocessed:                18
% 1.66/1.06  inst_num_of_loops:                      140
% 1.66/1.06  inst_num_of_learning_restarts:          0
% 1.66/1.06  inst_num_moves_active_passive:          33
% 1.66/1.06  inst_lit_activity:                      0
% 1.66/1.06  inst_lit_activity_moves:                0
% 1.66/1.06  inst_num_tautologies:                   0
% 1.66/1.06  inst_num_prop_implied:                  0
% 1.66/1.06  inst_num_existing_simplified:           0
% 1.66/1.06  inst_num_eq_res_simplified:             0
% 1.66/1.06  inst_num_child_elim:                    0
% 1.66/1.06  inst_num_of_dismatching_blockings:      36
% 1.66/1.06  inst_num_of_non_proper_insts:           211
% 1.66/1.06  inst_num_of_duplicates:                 0
% 1.66/1.06  inst_inst_num_from_inst_to_res:         0
% 1.66/1.06  inst_dismatching_checking_time:         0.
% 1.66/1.06  
% 1.66/1.06  ------ Resolution
% 1.66/1.06  
% 1.66/1.06  res_num_of_clauses:                     0
% 1.66/1.06  res_num_in_passive:                     0
% 1.66/1.06  res_num_in_active:                      0
% 1.66/1.06  res_num_of_loops:                       85
% 1.66/1.06  res_forward_subset_subsumed:            16
% 1.66/1.06  res_backward_subset_subsumed:           0
% 1.66/1.06  res_forward_subsumed:                   0
% 1.66/1.06  res_backward_subsumed:                  0
% 1.66/1.06  res_forward_subsumption_resolution:     1
% 1.66/1.06  res_backward_subsumption_resolution:    0
% 1.66/1.06  res_clause_to_clause_subsumption:       105
% 1.66/1.06  res_orphan_elimination:                 0
% 1.66/1.06  res_tautology_del:                      50
% 1.66/1.06  res_num_eq_res_simplified:              0
% 1.66/1.06  res_num_sel_changes:                    0
% 1.66/1.06  res_moves_from_active_to_pass:          0
% 1.66/1.06  
% 1.66/1.06  ------ Superposition
% 1.66/1.06  
% 1.66/1.06  sup_time_total:                         0.
% 1.66/1.06  sup_time_generating:                    0.
% 1.66/1.06  sup_time_sim_full:                      0.
% 1.66/1.06  sup_time_sim_immed:                     0.
% 1.66/1.06  
% 1.66/1.06  sup_num_of_clauses:                     18
% 1.66/1.06  sup_num_in_active:                      12
% 1.66/1.06  sup_num_in_passive:                     6
% 1.66/1.06  sup_num_of_loops:                       26
% 1.66/1.06  sup_fw_superposition:                   13
% 1.66/1.06  sup_bw_superposition:                   6
% 1.66/1.06  sup_immediate_simplified:               5
% 1.66/1.06  sup_given_eliminated:                   0
% 1.66/1.06  comparisons_done:                       0
% 1.66/1.06  comparisons_avoided:                    0
% 1.66/1.06  
% 1.66/1.06  ------ Simplifications
% 1.66/1.06  
% 1.66/1.06  
% 1.66/1.06  sim_fw_subset_subsumed:                 0
% 1.66/1.06  sim_bw_subset_subsumed:                 4
% 1.66/1.06  sim_fw_subsumed:                        1
% 1.66/1.06  sim_bw_subsumed:                        0
% 1.66/1.06  sim_fw_subsumption_res:                 0
% 1.66/1.06  sim_bw_subsumption_res:                 0
% 1.66/1.06  sim_tautology_del:                      1
% 1.66/1.06  sim_eq_tautology_del:                   2
% 1.66/1.06  sim_eq_res_simp:                        2
% 1.66/1.06  sim_fw_demodulated:                     0
% 1.66/1.06  sim_bw_demodulated:                     12
% 1.66/1.06  sim_light_normalised:                   5
% 1.66/1.06  sim_joinable_taut:                      0
% 1.66/1.06  sim_joinable_simp:                      0
% 1.66/1.06  sim_ac_normalised:                      0
% 1.66/1.06  sim_smt_subsumption:                    0
% 1.66/1.06  
%------------------------------------------------------------------------------
