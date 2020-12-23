%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0613+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 19.44s
% Output     : CNFRefutation 19.44s
% Verified   : 
% Statistics : Number of formulae       :   32 (  56 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 206 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1339,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f650])).

fof(f2016,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1339])).

fof(f3141,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2016])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f942,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f943,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f942])).

fof(f2215,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f943])).

fof(f3142,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2016])).

fof(f821,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f822,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v4_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f821])).

fof(f1537,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f822])).

fof(f1538,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1537])).

fof(f2082,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ~ v4_relat_1(sK166,X1)
        & v4_relat_1(sK166,X0)
        & v1_relat_1(sK166) ) ) ),
    introduced(choice_axiom,[])).

fof(f2081,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v4_relat_1(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v4_relat_1(X2,sK165)
          & v4_relat_1(X2,sK164)
          & v1_relat_1(X2) )
      & r1_tarski(sK164,sK165) ) ),
    introduced(choice_axiom,[])).

fof(f2083,plain,
    ( ~ v4_relat_1(sK166,sK165)
    & v4_relat_1(sK166,sK164)
    & v1_relat_1(sK166)
    & r1_tarski(sK164,sK165) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK164,sK165,sK166])],[f1538,f2082,f2081])).

fof(f3362,plain,(
    ~ v4_relat_1(sK166,sK165) ),
    inference(cnf_transformation,[],[f2083])).

fof(f3361,plain,(
    v4_relat_1(sK166,sK164) ),
    inference(cnf_transformation,[],[f2083])).

fof(f3360,plain,(
    v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f2083])).

fof(f3359,plain,(
    r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f2083])).

cnf(c_1032,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3141])).

cnf(c_64493,plain,
    ( ~ v4_relat_1(sK166,sK164)
    | r1_tarski(k1_relat_1(sK166),sK164)
    | ~ v1_relat_1(sK166) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f2215])).

cnf(c_55861,plain,
    ( ~ r1_tarski(X0,sK165)
    | ~ r1_tarski(k1_relat_1(sK166),X0)
    | r1_tarski(k1_relat_1(sK166),sK165) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_61138,plain,
    ( ~ r1_tarski(k1_relat_1(sK166),sK164)
    | r1_tarski(k1_relat_1(sK166),sK165)
    | ~ r1_tarski(sK164,sK165) ),
    inference(instantiation,[status(thm)],[c_55861])).

cnf(c_1031,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3142])).

cnf(c_55749,plain,
    ( v4_relat_1(sK166,sK165)
    | ~ r1_tarski(k1_relat_1(sK166),sK165)
    | ~ v1_relat_1(sK166) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1249,negated_conjecture,
    ( ~ v4_relat_1(sK166,sK165) ),
    inference(cnf_transformation,[],[f3362])).

cnf(c_1250,negated_conjecture,
    ( v4_relat_1(sK166,sK164) ),
    inference(cnf_transformation,[],[f3361])).

cnf(c_1251,negated_conjecture,
    ( v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f3360])).

cnf(c_1252,negated_conjecture,
    ( r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f3359])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_64493,c_61138,c_55749,c_1249,c_1250,c_1251,c_1252])).

%------------------------------------------------------------------------------
