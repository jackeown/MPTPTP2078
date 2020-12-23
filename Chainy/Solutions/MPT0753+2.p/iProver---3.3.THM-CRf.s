%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0753+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 23.31s
% Output     : CNFRefutation 23.31s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 369 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1132,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f2214,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1132])).

fof(f2215,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2214])).

fof(f2216,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2217,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f2215,f2216])).

fof(f2891,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK18(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2217])).

fof(f2890,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK18(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2217])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1569,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f2595,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1569])).

fof(f3931,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2595])).

fof(f1064,axiom,(
    ! [X0] :
      ( v5_ordinal1(X0)
    <=> v3_ordinal1(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2837,plain,(
    ! [X0] :
      ( ( v5_ordinal1(X0)
        | ~ v3_ordinal1(k1_relat_1(X0)) )
      & ( v3_ordinal1(k1_relat_1(X0))
        | ~ v5_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f1064])).

fof(f4618,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v3_ordinal1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f2837])).

fof(f1105,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_ordinal1(k1_relat_1(X0))
       => ( v5_ordinal1(X0)
          & v1_funct_1(X0)
          & v5_relat_1(X0,k2_relat_1(X0))
          & v1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1106,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v3_ordinal1(k1_relat_1(X0))
         => ( v5_ordinal1(X0)
            & v1_funct_1(X0)
            & v5_relat_1(X0,k2_relat_1(X0))
            & v1_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f1105])).

fof(f2176,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1106])).

fof(f2177,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2176])).

fof(f2879,plain,
    ( ? [X0] :
        ( ( ~ v5_ordinal1(X0)
          | ~ v1_funct_1(X0)
          | ~ v5_relat_1(X0,k2_relat_1(X0))
          | ~ v1_relat_1(X0) )
        & v3_ordinal1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v5_ordinal1(sK253)
        | ~ v1_funct_1(sK253)
        | ~ v5_relat_1(sK253,k2_relat_1(sK253))
        | ~ v1_relat_1(sK253) )
      & v3_ordinal1(k1_relat_1(sK253))
      & v1_funct_1(sK253)
      & v1_relat_1(sK253) ) ),
    introduced(choice_axiom,[])).

fof(f2880,plain,
    ( ( ~ v5_ordinal1(sK253)
      | ~ v1_funct_1(sK253)
      | ~ v5_relat_1(sK253,k2_relat_1(sK253))
      | ~ v1_relat_1(sK253) )
    & v3_ordinal1(k1_relat_1(sK253))
    & v1_funct_1(sK253)
    & v1_relat_1(sK253) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK253])],[f2177,f2879])).

fof(f4696,plain,
    ( ~ v5_ordinal1(sK253)
    | ~ v1_funct_1(sK253)
    | ~ v5_relat_1(sK253,k2_relat_1(sK253))
    | ~ v1_relat_1(sK253) ),
    inference(cnf_transformation,[],[f2880])).

fof(f4693,plain,(
    v1_relat_1(sK253) ),
    inference(cnf_transformation,[],[f2880])).

fof(f4694,plain,(
    v1_funct_1(sK253) ),
    inference(cnf_transformation,[],[f2880])).

fof(f4695,plain,(
    v3_ordinal1(k1_relat_1(sK253)) ),
    inference(cnf_transformation,[],[f2880])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK18(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2891])).

cnf(c_81036,plain,
    ( r1_tarski(k2_relat_1(sK253),k2_relat_1(sK253))
    | ~ r2_hidden(sK18(k2_relat_1(sK253),k2_relat_1(sK253)),k2_relat_1(sK253)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK18(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2890])).

cnf(c_81038,plain,
    ( r1_tarski(k2_relat_1(sK253),k2_relat_1(sK253))
    | r2_hidden(sK18(k2_relat_1(sK253),k2_relat_1(sK253)),k2_relat_1(sK253)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1035,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3931])).

cnf(c_79025,plain,
    ( v5_relat_1(sK253,k2_relat_1(sK253))
    | ~ r1_tarski(k2_relat_1(sK253),k2_relat_1(sK253))
    | ~ v1_relat_1(sK253) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_1721,plain,
    ( v5_ordinal1(X0)
    | ~ v3_ordinal1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4618])).

cnf(c_12324,plain,
    ( v5_ordinal1(X0)
    | ~ v3_ordinal1(k1_relat_1(X0)) ),
    inference(prop_impl,[status(thm)],[c_1721])).

cnf(c_1797,negated_conjecture,
    ( ~ v5_relat_1(sK253,k2_relat_1(sK253))
    | ~ v5_ordinal1(sK253)
    | ~ v1_funct_1(sK253)
    | ~ v1_relat_1(sK253) ),
    inference(cnf_transformation,[],[f4696])).

cnf(c_1800,negated_conjecture,
    ( v1_relat_1(sK253) ),
    inference(cnf_transformation,[],[f4693])).

cnf(c_1799,negated_conjecture,
    ( v1_funct_1(sK253) ),
    inference(cnf_transformation,[],[f4694])).

cnf(c_8600,negated_conjecture,
    ( ~ v5_relat_1(sK253,k2_relat_1(sK253))
    | ~ v5_ordinal1(sK253) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1797,c_1800,c_1799])).

cnf(c_19156,plain,
    ( ~ v5_relat_1(sK253,k2_relat_1(sK253))
    | ~ v3_ordinal1(k1_relat_1(X0))
    | sK253 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12324,c_8600])).

cnf(c_19157,plain,
    ( ~ v5_relat_1(sK253,k2_relat_1(sK253))
    | ~ v3_ordinal1(k1_relat_1(sK253)) ),
    inference(unflattening,[status(thm)],[c_19156])).

cnf(c_1798,negated_conjecture,
    ( v3_ordinal1(k1_relat_1(sK253)) ),
    inference(cnf_transformation,[],[f4695])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_81036,c_81038,c_79025,c_19157,c_1798,c_1800])).

%------------------------------------------------------------------------------
