%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0398+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:12 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   58 (  74 expanded)
%              Number of clauses        :   29 (  34 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 153 expanded)
%              Number of equality atoms :   30 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] : ~ r2_hidden(X2,X0)
     => r1_setfam_1(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] : r2_hidden(X2,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X2] : r2_hidden(X2,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,
    ( ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0)
   => ~ r1_setfam_1(k1_xboole_0,sK2) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f21])).

fof(f29,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f19])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_185,plain,
    ( ~ v1_xboole_0(X0_38)
    | k1_xboole_0 = X0_38 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_382,plain,
    ( ~ v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_188,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_363,plain,
    ( sK1(k1_zfmisc_1(o_0_0_xboole_0)) = sK1(k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_190,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_329,plain,
    ( sK1(k1_zfmisc_1(o_0_0_xboole_0)) != X0_38
    | sK1(k1_zfmisc_1(o_0_0_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != X0_38 ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_362,plain,
    ( sK1(k1_zfmisc_1(o_0_0_xboole_0)) != sK1(k1_zfmisc_1(o_0_0_xboole_0))
    | sK1(k1_zfmisc_1(o_0_0_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != sK1(k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | r1_setfam_1(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,negated_conjecture,
    ( ~ r1_setfam_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_82,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK2 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_83,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_82])).

cnf(c_2,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_103,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2)
    | k1_zfmisc_1(X2) != X3
    | sK1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_104,plain,
    ( ~ r2_hidden(X0,sK1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_121,plain,
    ( ~ v1_xboole_0(X0)
    | sK1(k1_zfmisc_1(X0)) != k1_xboole_0
    | sK0(k1_xboole_0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_83,c_104])).

cnf(c_122,plain,
    ( ~ v1_xboole_0(X0)
    | sK1(k1_zfmisc_1(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_184,plain,
    ( ~ v1_xboole_0(X0_38)
    | sK1(k1_zfmisc_1(X0_38)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_122])).

cnf(c_305,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | sK1(k1_zfmisc_1(o_0_0_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_91,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_92,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_133,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK1(X1) != X2
    | sK1(k1_zfmisc_1(X0)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_92,c_104])).

cnf(c_134,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1(k1_zfmisc_1(X0))) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_183,plain,
    ( ~ v1_xboole_0(X0_38)
    | v1_xboole_0(sK1(k1_zfmisc_1(X0_38))) ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_302,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_1,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_382,c_363,c_362,c_305,c_302,c_1])).


%------------------------------------------------------------------------------
