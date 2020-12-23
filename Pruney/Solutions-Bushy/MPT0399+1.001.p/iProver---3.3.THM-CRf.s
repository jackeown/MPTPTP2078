%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0399+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:12 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of clauses        :   29 (  32 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 147 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK0(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK0(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK1
      & r1_setfam_1(sK1,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k1_xboole_0 != sK1
    & r1_setfam_1(sK1,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).

fof(f27,plain,(
    r1_setfam_1(sK1,k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(o_1_0_setfam_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(o_1_0_setfam_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_245,plain,
    ( ~ v1_xboole_0(X0_38)
    | v1_xboole_0(X1_38)
    | X1_38 != X0_38 ),
    theory(equality)).

cnf(c_474,plain,
    ( v1_xboole_0(X0_38)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0_38 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_476,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_236,plain,
    ( ~ r2_hidden(X0_37,X0_38)
    | ~ v1_xboole_0(X0_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_436,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_1,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_238,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_360,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_237,plain,
    ( ~ v1_xboole_0(X0_38)
    | k1_xboole_0 = X0_38 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_361,plain,
    ( k1_xboole_0 = X0_38
    | v1_xboole_0(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_435,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_360,c_361])).

cnf(c_0,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK0(X1),X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,negated_conjecture,
    ( r1_setfam_1(sK1,k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_83,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2),X2)
    | sK1 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_84,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_83])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0_37,sK1)
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_84])).

cnf(c_416,plain,
    ( ~ r2_hidden(o_1_0_setfam_1(sK1),sK1)
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_2,plain,
    ( m1_subset_1(o_1_0_setfam_1(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_98,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | o_1_0_setfam_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_99,plain,
    ( r2_hidden(o_1_0_setfam_1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_98])).

cnf(c_233,plain,
    ( r2_hidden(o_1_0_setfam_1(X0_38),X0_38)
    | v1_xboole_0(X0_38) ),
    inference(subtyping,[status(esa)],[c_99])).

cnf(c_406,plain,
    ( r2_hidden(o_1_0_setfam_1(sK1),sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_397,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_235,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_476,c_436,c_435,c_416,c_406,c_397,c_235,c_1])).


%------------------------------------------------------------------------------
