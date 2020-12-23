%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0045+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:33 EST 2020

% Result     : Theorem 0.34s
% Output     : CNFRefutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   58 (  64 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,k4_xboole_0(X2,X1))
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t38_xboole_1])).

fof(c_0_5,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49,X50] :
      ( ( r2_hidden(X46,X43)
        | ~ r2_hidden(X46,X45)
        | X45 != k4_xboole_0(X43,X44) )
      & ( ~ r2_hidden(X46,X44)
        | ~ r2_hidden(X46,X45)
        | X45 != k4_xboole_0(X43,X44) )
      & ( ~ r2_hidden(X47,X43)
        | r2_hidden(X47,X44)
        | r2_hidden(X47,X45)
        | X45 != k4_xboole_0(X43,X44) )
      & ( ~ r2_hidden(esk5_3(X48,X49,X50),X50)
        | ~ r2_hidden(esk5_3(X48,X49,X50),X48)
        | r2_hidden(esk5_3(X48,X49,X50),X49)
        | X50 = k4_xboole_0(X48,X49) )
      & ( r2_hidden(esk5_3(X48,X49,X50),X48)
        | r2_hidden(esk5_3(X48,X49,X50),X50)
        | X50 = k4_xboole_0(X48,X49) )
      & ( ~ r2_hidden(esk5_3(X48,X49,X50),X49)
        | r2_hidden(esk5_3(X48,X49,X50),X50)
        | X50 = k4_xboole_0(X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(X21,X19)
        | r2_hidden(X21,X20) )
      & ( r2_hidden(esk2_2(X22,X23),X22)
        | r1_tarski(X22,X23) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,negated_conjecture,
    ( r1_tarski(esk16_0,k4_xboole_0(esk17_0,esk16_0))
    & esk16_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk16_0,k4_xboole_0(esk17_0,esk16_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X94] :
      ( X94 = k1_xboole_0
      | r2_hidden(esk13_1(X94),X94) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(X1,esk16_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk13_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk16_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
