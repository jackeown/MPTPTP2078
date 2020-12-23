%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0732+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:00 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   46 (  72 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 226 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_ordinal1(X2)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X1) )
         => r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1)
        & v1_ordinal1(X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK0,sK1)
      & v1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK0,sK1)
    & v1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f28,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,negated_conjecture,
    ( v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_93,plain,
    ( ~ r2_hidden(X0,sK2)
    | r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_107,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

cnf(c_214,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
    | m1_subset_1(sK0,X0) ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_205,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | m1_subset_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_161,plain,
    ( ~ v1_xboole_0(sK2) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_152,plain,
    ( ~ m1_subset_1(sK0,sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_214,c_205,c_161,c_152])).


%------------------------------------------------------------------------------
