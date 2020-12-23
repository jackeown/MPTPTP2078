%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:09 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 341 expanded)
%              Number of clauses        :   63 ( 125 expanded)
%              Number of leaves         :   14 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  341 (1479 expanded)
%              Number of equality atoms :  140 ( 327 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f67,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
        | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
        | ~ v1_funct_1(sK6) )
      & r1_tarski(k2_relat_1(sK6),sK5)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
      | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
      | ~ v1_funct_1(sK6) )
    & r1_tarski(k2_relat_1(sK6),sK5)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f46,f67])).

fof(f123,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f121,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f139,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f127,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f118,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f122,plain,(
    r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15218,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)),X0)
    | r1_tarski(sK6,X0)
    | ~ r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_21183,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)),k2_zfmisc_1(k1_relat_1(sK6),sK5))
    | ~ r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))
    | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_15218])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_13631,plain,
    ( r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK6)),k2_zfmisc_1(X0,sK5))
    | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_15606,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)),k2_zfmisc_1(k1_relat_1(sK6),sK5))
    | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_13631])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_13812,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))
    | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_11884,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_45,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_51,negated_conjecture,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_53,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_277,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51,c_53])).

cnf(c_278,negated_conjecture,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK6) != X1
    | sK5 != X2
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_278])).

cnf(c_747,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | k1_relset_1(k1_relat_1(sK6),sK5,sK6) != k1_relat_1(sK6)
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_755,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | k1_xboole_0 = sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_747,c_41])).

cnf(c_44,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK6) != k1_xboole_0
    | sK5 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_278])).

cnf(c_707,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | k1_relat_1(sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_162,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_163,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_167,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_169,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_49,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_759,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK5
    | k1_relat_1(X0) != k1_relat_1(sK6)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_49,c_278])).

cnf(c_760,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) != sK5
    | k1_relat_1(sK6) != k1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_54,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_762,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | k2_relat_1(sK6) != sK5
    | k1_relat_1(sK6) != k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_54,c_53])).

cnf(c_2193,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | k2_relat_1(sK6) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_762])).

cnf(c_3785,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7040,plain,
    ( X0 != sK5
    | X0 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3785])).

cnf(c_7279,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_7040])).

cnf(c_8364,plain,
    ( X0 = X1
    | X1 != k1_xboole_0
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3785])).

cnf(c_8477,plain,
    ( k2_relat_1(sK6) = sK5
    | k2_relat_1(sK6) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8364])).

cnf(c_52,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_7975,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_7982,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8444,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7975,c_7982])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7980,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8493,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8444,c_7980])).

cnf(c_3784,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_9230,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3784])).

cnf(c_3786,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10546,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_xboole_0,X2)
    | X1 != X2
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3786])).

cnf(c_11674,plain,
    ( r1_tarski(sK5,X0)
    | ~ r1_tarski(k1_xboole_0,X1)
    | X0 != X1
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10546])).

cnf(c_11675,plain,
    ( X0 != X1
    | sK5 != k1_xboole_0
    | r1_tarski(sK5,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11674])).

cnf(c_11677,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11675])).

cnf(c_11799,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_162,c_163,c_169,c_755,c_2193,c_7279,c_8477,c_8493,c_9230,c_11677])).

cnf(c_11804,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_162,c_163,c_169,c_2193,c_7279,c_8477,c_8493,c_9230,c_11677])).

cnf(c_11882,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11804])).

cnf(c_11912,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11884,c_11882])).

cnf(c_11913,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11912])).

cnf(c_48,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_53])).

cnf(c_1002,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_1001])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21183,c_15606,c_13812,c_11913,c_1002,c_52,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.02/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.00  
% 4.02/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/1.00  
% 4.02/1.00  ------  iProver source info
% 4.02/1.00  
% 4.02/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.02/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/1.00  git: non_committed_changes: false
% 4.02/1.00  git: last_make_outside_of_git: false
% 4.02/1.00  
% 4.02/1.00  ------ 
% 4.02/1.00  ------ Parsing...
% 4.02/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  ------ Proving...
% 4.02/1.00  ------ Problem Properties 
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  clauses                                 49
% 4.02/1.00  conjectures                             4
% 4.02/1.00  EPR                                     9
% 4.02/1.00  Horn                                    40
% 4.02/1.00  unary                                   13
% 4.02/1.00  binary                                  17
% 4.02/1.00  lits                                    119
% 4.02/1.00  lits eq                                 41
% 4.02/1.00  fd_pure                                 0
% 4.02/1.00  fd_pseudo                               0
% 4.02/1.00  fd_cond                                 7
% 4.02/1.00  fd_pseudo_cond                          4
% 4.02/1.00  AC symbols                              0
% 4.02/1.00  
% 4.02/1.00  ------ Input Options Time Limit: Unbounded
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 17 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.02/1.00  Current options:
% 4.02/1.00  ------ 
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing...
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 30 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing...
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 16 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.00  
% 4.02/1.00  ------ Proving...
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  % SZS status Theorem for theBenchmark.p
% 4.02/1.00  
% 4.02/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/1.00  
% 4.02/1.00  fof(f3,axiom,(
% 4.02/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f25,plain,(
% 4.02/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.02/1.00    inference(ennf_transformation,[],[f3])).
% 4.02/1.00  
% 4.02/1.00  fof(f26,plain,(
% 4.02/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.02/1.00    inference(flattening,[],[f25])).
% 4.02/1.00  
% 4.02/1.00  fof(f75,plain,(
% 4.02/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f26])).
% 4.02/1.00  
% 4.02/1.00  fof(f7,axiom,(
% 4.02/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f28,plain,(
% 4.02/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 4.02/1.00    inference(ennf_transformation,[],[f7])).
% 4.02/1.00  
% 4.02/1.00  fof(f82,plain,(
% 4.02/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f28])).
% 4.02/1.00  
% 4.02/1.00  fof(f8,axiom,(
% 4.02/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f55,plain,(
% 4.02/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.02/1.00    inference(nnf_transformation,[],[f8])).
% 4.02/1.00  
% 4.02/1.00  fof(f83,plain,(
% 4.02/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.02/1.00    inference(cnf_transformation,[],[f55])).
% 4.02/1.00  
% 4.02/1.00  fof(f84,plain,(
% 4.02/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f55])).
% 4.02/1.00  
% 4.02/1.00  fof(f19,axiom,(
% 4.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f41,plain,(
% 4.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/1.00    inference(ennf_transformation,[],[f19])).
% 4.02/1.00  
% 4.02/1.00  fof(f42,plain,(
% 4.02/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/1.00    inference(flattening,[],[f41])).
% 4.02/1.00  
% 4.02/1.00  fof(f66,plain,(
% 4.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/1.00    inference(nnf_transformation,[],[f42])).
% 4.02/1.00  
% 4.02/1.00  fof(f113,plain,(
% 4.02/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/1.00    inference(cnf_transformation,[],[f66])).
% 4.02/1.00  
% 4.02/1.00  fof(f21,conjecture,(
% 4.02/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f22,negated_conjecture,(
% 4.02/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.02/1.00    inference(negated_conjecture,[],[f21])).
% 4.02/1.00  
% 4.02/1.00  fof(f45,plain,(
% 4.02/1.00    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.02/1.00    inference(ennf_transformation,[],[f22])).
% 4.02/1.00  
% 4.02/1.00  fof(f46,plain,(
% 4.02/1.00    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.02/1.00    inference(flattening,[],[f45])).
% 4.02/1.00  
% 4.02/1.00  fof(f67,plain,(
% 4.02/1.00    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) | ~v1_funct_2(sK6,k1_relat_1(sK6),sK5) | ~v1_funct_1(sK6)) & r1_tarski(k2_relat_1(sK6),sK5) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 4.02/1.00    introduced(choice_axiom,[])).
% 4.02/1.00  
% 4.02/1.00  fof(f68,plain,(
% 4.02/1.00    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) | ~v1_funct_2(sK6,k1_relat_1(sK6),sK5) | ~v1_funct_1(sK6)) & r1_tarski(k2_relat_1(sK6),sK5) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 4.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f46,f67])).
% 4.02/1.00  
% 4.02/1.00  fof(f123,plain,(
% 4.02/1.00    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) | ~v1_funct_2(sK6,k1_relat_1(sK6),sK5) | ~v1_funct_1(sK6)),
% 4.02/1.00    inference(cnf_transformation,[],[f68])).
% 4.02/1.00  
% 4.02/1.00  fof(f121,plain,(
% 4.02/1.00    v1_funct_1(sK6)),
% 4.02/1.00    inference(cnf_transformation,[],[f68])).
% 4.02/1.00  
% 4.02/1.00  fof(f18,axiom,(
% 4.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f40,plain,(
% 4.02/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/1.00    inference(ennf_transformation,[],[f18])).
% 4.02/1.00  
% 4.02/1.00  fof(f110,plain,(
% 4.02/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/1.00    inference(cnf_transformation,[],[f40])).
% 4.02/1.00  
% 4.02/1.00  fof(f114,plain,(
% 4.02/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/1.00    inference(cnf_transformation,[],[f66])).
% 4.02/1.00  
% 4.02/1.00  fof(f139,plain,(
% 4.02/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 4.02/1.00    inference(equality_resolution,[],[f114])).
% 4.02/1.00  
% 4.02/1.00  fof(f6,axiom,(
% 4.02/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f53,plain,(
% 4.02/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.02/1.00    inference(nnf_transformation,[],[f6])).
% 4.02/1.00  
% 4.02/1.00  fof(f54,plain,(
% 4.02/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.02/1.00    inference(flattening,[],[f53])).
% 4.02/1.00  
% 4.02/1.00  fof(f78,plain,(
% 4.02/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f54])).
% 4.02/1.00  
% 4.02/1.00  fof(f79,plain,(
% 4.02/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.02/1.00    inference(cnf_transformation,[],[f54])).
% 4.02/1.00  
% 4.02/1.00  fof(f127,plain,(
% 4.02/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.02/1.00    inference(equality_resolution,[],[f79])).
% 4.02/1.00  
% 4.02/1.00  fof(f4,axiom,(
% 4.02/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f76,plain,(
% 4.02/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f4])).
% 4.02/1.00  
% 4.02/1.00  fof(f20,axiom,(
% 4.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f43,plain,(
% 4.02/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.02/1.00    inference(ennf_transformation,[],[f20])).
% 4.02/1.00  
% 4.02/1.00  fof(f44,plain,(
% 4.02/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.02/1.00    inference(flattening,[],[f43])).
% 4.02/1.00  
% 4.02/1.00  fof(f118,plain,(
% 4.02/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f44])).
% 4.02/1.00  
% 4.02/1.00  fof(f120,plain,(
% 4.02/1.00    v1_relat_1(sK6)),
% 4.02/1.00    inference(cnf_transformation,[],[f68])).
% 4.02/1.00  
% 4.02/1.00  fof(f122,plain,(
% 4.02/1.00    r1_tarski(k2_relat_1(sK6),sK5)),
% 4.02/1.00    inference(cnf_transformation,[],[f68])).
% 4.02/1.00  
% 4.02/1.00  fof(f5,axiom,(
% 4.02/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 4.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.00  
% 4.02/1.00  fof(f27,plain,(
% 4.02/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 4.02/1.00    inference(ennf_transformation,[],[f5])).
% 4.02/1.00  
% 4.02/1.00  fof(f77,plain,(
% 4.02/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f27])).
% 4.02/1.00  
% 4.02/1.00  fof(f119,plain,(
% 4.02/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.02/1.00    inference(cnf_transformation,[],[f44])).
% 4.02/1.00  
% 4.02/1.00  cnf(c_6,plain,
% 4.02/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 4.02/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15218,plain,
% 4.02/1.00      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)),X0)
% 4.02/1.00      | r1_tarski(sK6,X0)
% 4.02/1.00      | ~ r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_21183,plain,
% 4.02/1.00      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)),k2_zfmisc_1(k1_relat_1(sK6),sK5))
% 4.02/1.00      | ~ r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))
% 4.02/1.00      | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK5)) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_15218]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_12,plain,
% 4.02/1.00      ( ~ r1_tarski(X0,X1)
% 4.02/1.00      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 4.02/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_13631,plain,
% 4.02/1.00      ( r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK6)),k2_zfmisc_1(X0,sK5))
% 4.02/1.00      | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15606,plain,
% 4.02/1.00      ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)),k2_zfmisc_1(k1_relat_1(sK6),sK5))
% 4.02/1.00      | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_13631]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.02/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_13812,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))
% 4.02/1.00      | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_14,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.02/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11884,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.02/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_45,plain,
% 4.02/1.00      ( v1_funct_2(X0,X1,X2)
% 4.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | k1_relset_1(X1,X2,X0) != X1
% 4.02/1.00      | k1_xboole_0 = X2 ),
% 4.02/1.00      inference(cnf_transformation,[],[f113]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_51,negated_conjecture,
% 4.02/1.00      ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
% 4.02/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | ~ v1_funct_1(sK6) ),
% 4.02/1.00      inference(cnf_transformation,[],[f123]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_53,negated_conjecture,
% 4.02/1.00      ( v1_funct_1(sK6) ),
% 4.02/1.00      inference(cnf_transformation,[],[f121]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_277,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5) ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_51,c_53]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_278,negated_conjecture,
% 4.02/1.00      ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
% 4.02/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) ),
% 4.02/1.00      inference(renaming,[status(thm)],[c_277]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_746,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | k1_relset_1(X1,X2,X0) != X1
% 4.02/1.00      | k1_relat_1(sK6) != X1
% 4.02/1.00      | sK5 != X2
% 4.02/1.00      | sK6 != X0
% 4.02/1.00      | k1_xboole_0 = X2 ),
% 4.02/1.00      inference(resolution_lifted,[status(thm)],[c_45,c_278]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_747,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | k1_relset_1(k1_relat_1(sK6),sK5,sK6) != k1_relat_1(sK6)
% 4.02/1.00      | k1_xboole_0 = sK5 ),
% 4.02/1.00      inference(unflattening,[status(thm)],[c_746]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_41,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f110]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_755,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | k1_xboole_0 = sK5 ),
% 4.02/1.00      inference(forward_subsumption_resolution,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_747,c_41]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_44,plain,
% 4.02/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 4.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.02/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 4.02/1.00      inference(cnf_transformation,[],[f139]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_706,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.02/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 4.02/1.00      | k1_relat_1(sK6) != k1_xboole_0
% 4.02/1.00      | sK5 != X1
% 4.02/1.00      | sK6 != X0 ),
% 4.02/1.00      inference(resolution_lifted,[status(thm)],[c_44,c_278]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_707,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 4.02/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 4.02/1.00      | k1_relat_1(sK6) != k1_xboole_0 ),
% 4.02/1.00      inference(unflattening,[status(thm)],[c_706]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11,plain,
% 4.02/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 4.02/1.00      | k1_xboole_0 = X0
% 4.02/1.00      | k1_xboole_0 = X1 ),
% 4.02/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_162,plain,
% 4.02/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.02/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_10,plain,
% 4.02/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.02/1.00      inference(cnf_transformation,[],[f127]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_163,plain,
% 4.02/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7,plain,
% 4.02/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_167,plain,
% 4.02/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_169,plain,
% 4.02/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_167]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_49,plain,
% 4.02/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 4.02/1.00      | ~ v1_funct_1(X0)
% 4.02/1.00      | ~ v1_relat_1(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f118]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_759,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | ~ v1_funct_1(X0)
% 4.02/1.00      | ~ v1_relat_1(X0)
% 4.02/1.00      | k2_relat_1(X0) != sK5
% 4.02/1.00      | k1_relat_1(X0) != k1_relat_1(sK6)
% 4.02/1.00      | sK6 != X0 ),
% 4.02/1.00      inference(resolution_lifted,[status(thm)],[c_49,c_278]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_760,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | ~ v1_funct_1(sK6)
% 4.02/1.00      | ~ v1_relat_1(sK6)
% 4.02/1.00      | k2_relat_1(sK6) != sK5
% 4.02/1.00      | k1_relat_1(sK6) != k1_relat_1(sK6) ),
% 4.02/1.00      inference(unflattening,[status(thm)],[c_759]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_54,negated_conjecture,
% 4.02/1.00      ( v1_relat_1(sK6) ),
% 4.02/1.00      inference(cnf_transformation,[],[f120]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_762,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | k2_relat_1(sK6) != sK5
% 4.02/1.00      | k1_relat_1(sK6) != k1_relat_1(sK6) ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_760,c_54,c_53]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2193,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
% 4.02/1.00      | k2_relat_1(sK6) != sK5 ),
% 4.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_762]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_3785,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7040,plain,
% 4.02/1.00      ( X0 != sK5 | X0 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_3785]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7279,plain,
% 4.02/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_7040]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_8364,plain,
% 4.02/1.00      ( X0 = X1 | X1 != k1_xboole_0 | X0 != k1_xboole_0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_3785]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_8477,plain,
% 4.02/1.00      ( k2_relat_1(sK6) = sK5
% 4.02/1.00      | k2_relat_1(sK6) != k1_xboole_0
% 4.02/1.00      | sK5 != k1_xboole_0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_8364]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_52,negated_conjecture,
% 4.02/1.00      ( r1_tarski(k2_relat_1(sK6),sK5) ),
% 4.02/1.00      inference(cnf_transformation,[],[f122]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7975,plain,
% 4.02/1.00      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7982,plain,
% 4.02/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.02/1.00      | r1_tarski(X1,X2) != iProver_top
% 4.02/1.00      | r1_tarski(X0,X2) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_8444,plain,
% 4.02/1.00      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 4.02/1.00      | r1_tarski(sK5,X0) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_7975,c_7982]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_8,plain,
% 4.02/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 4.02/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7980,plain,
% 4.02/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_8493,plain,
% 4.02/1.00      ( k2_relat_1(sK6) = k1_xboole_0
% 4.02/1.00      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_8444,c_7980]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_3784,plain,( X0 = X0 ),theory(equality) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_9230,plain,
% 4.02/1.00      ( sK5 = sK5 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_3784]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_3786,plain,
% 4.02/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.02/1.00      theory(equality) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_10546,plain,
% 4.02/1.00      ( r1_tarski(X0,X1)
% 4.02/1.00      | ~ r1_tarski(k1_xboole_0,X2)
% 4.02/1.00      | X1 != X2
% 4.02/1.00      | X0 != k1_xboole_0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_3786]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11674,plain,
% 4.02/1.00      ( r1_tarski(sK5,X0)
% 4.02/1.00      | ~ r1_tarski(k1_xboole_0,X1)
% 4.02/1.00      | X0 != X1
% 4.02/1.00      | sK5 != k1_xboole_0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_10546]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11675,plain,
% 4.02/1.00      ( X0 != X1
% 4.02/1.00      | sK5 != k1_xboole_0
% 4.02/1.00      | r1_tarski(sK5,X0) = iProver_top
% 4.02/1.00      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_11674]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11677,plain,
% 4.02/1.00      ( sK5 != k1_xboole_0
% 4.02/1.00      | k1_xboole_0 != k1_xboole_0
% 4.02/1.00      | r1_tarski(sK5,k1_xboole_0) = iProver_top
% 4.02/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_11675]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11799,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_707,c_162,c_163,c_169,c_755,c_2193,c_7279,c_8477,
% 4.02/1.00                 c_8493,c_9230,c_11677]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11804,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_755,c_162,c_163,c_169,c_2193,c_7279,c_8477,c_8493,
% 4.02/1.00                 c_9230,c_11677]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11882,plain,
% 4.02/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_11804]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11912,plain,
% 4.02/1.00      ( r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK5)) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_11884,c_11882]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11913,plain,
% 4.02/1.00      ( ~ r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK5)) ),
% 4.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11912]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_48,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 4.02/1.00      | ~ v1_funct_1(X0)
% 4.02/1.00      | ~ v1_relat_1(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f119]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1001,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 4.02/1.00      | ~ v1_relat_1(X0)
% 4.02/1.00      | sK6 != X0 ),
% 4.02/1.00      inference(resolution_lifted,[status(thm)],[c_48,c_53]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1002,plain,
% 4.02/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))
% 4.02/1.00      | ~ v1_relat_1(sK6) ),
% 4.02/1.00      inference(unflattening,[status(thm)],[c_1001]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(contradiction,plain,
% 4.02/1.00      ( $false ),
% 4.02/1.00      inference(minisat,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_21183,c_15606,c_13812,c_11913,c_1002,c_52,c_54]) ).
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/1.00  
% 4.02/1.00  ------                               Statistics
% 4.02/1.00  
% 4.02/1.00  ------ Selected
% 4.02/1.00  
% 4.02/1.00  total_time:                             0.453
% 4.02/1.00  
%------------------------------------------------------------------------------
