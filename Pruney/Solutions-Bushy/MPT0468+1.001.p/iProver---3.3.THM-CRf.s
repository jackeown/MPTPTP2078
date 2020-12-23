%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0468+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:22 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 126 expanded)
%              Number of clauses        :   20 (  38 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 372 expanded)
%              Number of equality atoms :   50 ( 121 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f17,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17,f16])).

fof(f21,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK1(X4),sK2(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => m1_subset_1(o_1_1_relat_1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(o_1_1_relat_1(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(o_1_1_relat_1(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f19,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK3
      & ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k1_xboole_0 != sK3
    & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f19])).

fof(f27,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK3) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( m1_subset_1(o_1_1_relat_1(X0),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_94,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | ~ v1_relat_1(X2)
    | X1 != X2
    | o_1_1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_95,plain,
    ( r2_hidden(o_1_1_relat_1(X0),X0)
    | v1_xboole_0(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_94])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_113,plain,
    ( r2_hidden(o_1_1_relat_1(X0),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_95,c_5])).

cnf(c_135,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 != X0
    | k4_tarski(sK1(X2),sK2(X2)) = X2
    | o_1_1_relat_1(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_113])).

cnf(c_136,plain,
    ( ~ v1_relat_1(X0)
    | k4_tarski(sK1(o_1_1_relat_1(X0)),sK2(o_1_1_relat_1(X0))) = o_1_1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_177,plain,
    ( k4_tarski(sK1(o_1_1_relat_1(X0)),sK2(o_1_1_relat_1(X0))) = o_1_1_relat_1(X0)
    | sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_136,c_8])).

cnf(c_178,plain,
    ( k4_tarski(sK1(o_1_1_relat_1(sK3)),sK2(o_1_1_relat_1(sK3))) = o_1_1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_138,plain,
    ( ~ v1_relat_1(sK3)
    | k4_tarski(sK1(o_1_1_relat_1(sK3)),sK2(o_1_1_relat_1(sK3))) = o_1_1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_179,plain,
    ( k4_tarski(sK1(o_1_1_relat_1(sK3)),sK2(o_1_1_relat_1(sK3))) = o_1_1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_8,c_6,c_138])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_150,plain,
    ( ~ v1_relat_1(X0)
    | k4_tarski(X1,X2) != o_1_1_relat_1(X0)
    | sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_113])).

cnf(c_151,plain,
    ( ~ v1_relat_1(sK3)
    | k4_tarski(X0,X1) != o_1_1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_155,plain,
    ( k4_tarski(X0,X1) != o_1_1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_151,c_8,c_6])).

cnf(c_183,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_179,c_155])).


%------------------------------------------------------------------------------
