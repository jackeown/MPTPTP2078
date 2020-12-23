%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0485+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:41 EST 2020

% Result     : Theorem 27.87s
% Output     : CNFRefutation 27.87s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 115 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f744,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1279,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f744])).

fof(f1280,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1279])).

fof(f1281,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1282,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1280,f1281])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1282])).

fof(f1697,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1282])).

fof(f723,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1255,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f1256,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1255])).

fof(f2821,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1256])).

fof(f724,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f725,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f724])).

fof(f1257,plain,(
    ? [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f725])).

fof(f1686,plain,
    ( ? [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( k5_relat_1(sK152,k6_relat_1(k2_relat_1(sK152))) != sK152
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1687,plain,
    ( k5_relat_1(sK152,k6_relat_1(k2_relat_1(sK152))) != sK152
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK152])],[f1257,f1686])).

fof(f2823,plain,(
    k5_relat_1(sK152,k6_relat_1(k2_relat_1(sK152))) != sK152 ),
    inference(cnf_transformation,[],[f1687])).

fof(f2822,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1687])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1698])).

cnf(c_51744,plain,
    ( r1_tarski(k2_relat_1(sK152),k2_relat_1(sK152))
    | ~ r2_hidden(sK11(k2_relat_1(sK152),k2_relat_1(sK152)),k2_relat_1(sK152)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1697])).

cnf(c_51746,plain,
    ( r1_tarski(k2_relat_1(sK152),k2_relat_1(sK152))
    | r2_hidden(sK11(k2_relat_1(sK152),k2_relat_1(sK152)),k2_relat_1(sK152)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1119,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f2821])).

cnf(c_48329,plain,
    ( ~ r1_tarski(k2_relat_1(sK152),k2_relat_1(sK152))
    | ~ v1_relat_1(sK152)
    | k5_relat_1(sK152,k6_relat_1(k2_relat_1(sK152))) = sK152 ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_1120,negated_conjecture,
    ( k5_relat_1(sK152,k6_relat_1(k2_relat_1(sK152))) != sK152 ),
    inference(cnf_transformation,[],[f2823])).

cnf(c_1121,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2822])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51744,c_51746,c_48329,c_1120,c_1121])).

%------------------------------------------------------------------------------
