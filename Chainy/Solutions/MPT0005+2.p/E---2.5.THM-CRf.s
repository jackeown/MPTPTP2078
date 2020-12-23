%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0005+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  40 expanded)
%              Number of clauses        :   11 (  16 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 188 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_xboole_0,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(X1,X2)
        & r2_hidden(X3,k2_xboole_0(X1,X2))
        & ~ ( r2_hidden(X3,X1)
            & ~ r2_hidden(X3,X2) )
        & ~ ( r2_hidden(X3,X2)
            & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_xboole_0(X1,X2)
          & r2_hidden(X3,k2_xboole_0(X1,X2))
          & ~ ( r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X2) )
          & ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t5_xboole_0])).

fof(c_0_4,plain,(
    ! [X65,X66,X68,X69,X70] :
      ( ( r2_hidden(esk9_2(X65,X66),X65)
        | r1_xboole_0(X65,X66) )
      & ( r2_hidden(esk9_2(X65,X66),X66)
        | r1_xboole_0(X65,X66) )
      & ( ~ r2_hidden(X70,X68)
        | ~ r2_hidden(X70,X69)
        | ~ r1_xboole_0(X68,X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,
    ( r1_xboole_0(esk11_0,esk12_0)
    & r2_hidden(esk13_0,k2_xboole_0(esk11_0,esk12_0))
    & ( ~ r2_hidden(esk13_0,esk11_0)
      | r2_hidden(esk13_0,esk12_0) )
    & ( ~ r2_hidden(esk13_0,esk12_0)
      | r2_hidden(esk13_0,esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X19 != k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X19)
        | X19 != k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X22)
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X23)
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_xboole_0(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X23)
        | X24 = k2_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_xboole_0(esk11_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ r2_hidden(X1,esk12_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk13_0,esk12_0)
    | ~ r2_hidden(esk13_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk13_0,k2_xboole_0(esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk13_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk13_0,esk11_0)
    | ~ r2_hidden(esk13_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk13_0,esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
