%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1007+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:38 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 216 expanded)
%              Number of clauses        :   51 (  82 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  242 ( 781 expanded)
%              Number of equality atoms :  109 ( 255 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_relat_1(X1) = k1_tarski(X0)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
     => r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_385,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_592,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_590,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_797,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_592,c_590])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_tarski(sK0) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_301,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_303,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_15,c_14])).

cnf(c_380,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0) ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_866,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_797,c_380])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_tarski(X1) != k1_relat_1(X0)
    | k1_tarski(k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_217,plain,
    ( ~ v1_relat_1(X0)
    | k1_tarski(X1) != k1_relat_1(X0)
    | k1_tarski(k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_218,plain,
    ( ~ v1_relat_1(sK2)
    | k1_tarski(X0) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_tarski(X3) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X3)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_218])).

cnf(c_237,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_tarski(X2) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k1_tarski(X0_47) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0_47)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_390,plain,
    ( k1_tarski(X0_47) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0_47)) = k2_relat_1(sK2)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_383])).

cnf(c_596,plain,
    ( k1_tarski(X0_47) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0_47)) = k2_relat_1(sK2)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_392,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_383])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_383])).

cnf(c_668,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_761,plain,
    ( k1_tarski(k1_funct_1(sK2,X0_47)) = k2_relat_1(sK2)
    | k1_tarski(X0_47) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_15,c_392,c_390,c_668])).

cnf(c_762,plain,
    ( k1_tarski(X0_47) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0_47)) = k2_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_761])).

cnf(c_935,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_866,c_762])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_199,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | k1_funct_1(sK2,sK0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_200,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1(sK2,sK0)),sK1) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_tarski(k1_funct_1(sK2,sK0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_200])).

cnf(c_209,plain,
    ( ~ m1_subset_1(k1_tarski(k1_funct_1(sK2,sK0)),k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_384,plain,
    ( ~ m1_subset_1(k1_tarski(k1_funct_1(sK2,sK0)),k1_zfmisc_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_209])).

cnf(c_593,plain,
    ( m1_subset_1(k1_tarski(k1_funct_1(sK2,sK0)),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_974,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_935,c_593])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_591,plain,
    ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_854,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_592,c_591])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k2_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X2_46)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_589,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X2_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_914,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_589])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_974,c_914,c_20])).


%------------------------------------------------------------------------------
