%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0070+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:17 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 ( 244 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f121])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f187])).

fof(f189,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f188,f189])).

fof(f246,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f129,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f117])).

fof(f220,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f127,f220])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f221])).

fof(f292,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f221])).

fof(f293,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f221])).

fof(f105,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f105])).

fof(f175,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f176,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f175])).

fof(f236,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK15,sK17)
      & r1_xboole_0(sK16,sK17)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f237,plain,
    ( ~ r1_xboole_0(sK15,sK17)
    & r1_xboole_0(sK16,sK17)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f176,f236])).

fof(f382,plain,(
    ~ r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f237])).

fof(f381,plain,(
    r1_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f237])).

fof(f380,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f237])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f246])).

cnf(c_5586,plain,
    ( ~ r1_tarski(sK15,X0)
    | r2_hidden(sK9(sK15,sK17),X0)
    | ~ r2_hidden(sK9(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8968,plain,
    ( ~ r1_tarski(sK15,sK16)
    | r2_hidden(sK9(sK15,sK17),sK16)
    | ~ r2_hidden(sK9(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_5586])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f300])).

cnf(c_52,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f294])).

cnf(c_669,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r1_xboole_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57,c_52])).

cnf(c_670,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_669])).

cnf(c_5524,plain,
    ( ~ r1_xboole_0(X0,sK17)
    | ~ r2_hidden(sK9(sK15,sK17),X0)
    | ~ r2_hidden(sK9(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_7398,plain,
    ( ~ r1_xboole_0(sK16,sK17)
    | ~ r2_hidden(sK9(sK15,sK17),sK16)
    | ~ r2_hidden(sK9(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_5524])).

cnf(c_54,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X0) ),
    inference(cnf_transformation,[],[f292])).

cnf(c_5139,plain,
    ( r1_xboole_0(sK15,sK17)
    | r2_hidden(sK9(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_53,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X1) ),
    inference(cnf_transformation,[],[f293])).

cnf(c_5132,plain,
    ( r1_xboole_0(sK15,sK17)
    | r2_hidden(sK9(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_139,negated_conjecture,
    ( ~ r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f382])).

cnf(c_140,negated_conjecture,
    ( r1_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f381])).

cnf(c_141,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f380])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8968,c_7398,c_5139,c_5132,c_139,c_140,c_141])).

%------------------------------------------------------------------------------
