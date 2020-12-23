%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t215_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:59 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  75 expanded)
%              Number of clauses        :   20 (  34 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 259 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t215_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t215_relat_1.p',t215_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t215_relat_1.p',d1_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/relat_1__t215_relat_1.p',t3_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t215_relat_1.p',d5_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t215_relat_1.p',symmetry_r1_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t215_relat_1])).

fof(c_0_6,plain,(
    ! [X9,X10,X13,X15,X16] :
      ( ( ~ v1_relat_1(X9)
        | ~ r2_hidden(X10,X9)
        | X10 = k4_tarski(esk3_2(X9,X10),esk4_2(X9,X10)) )
      & ( r2_hidden(esk5_1(X13),X13)
        | v1_relat_1(X13) )
      & ( esk5_1(X13) != k4_tarski(X15,X16)
        | v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))
    & ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X36,X37,X39,X40,X41] :
      ( ( r2_hidden(esk10_2(X36,X37),X36)
        | r1_xboole_0(X36,X37) )
      & ( r2_hidden(esk10_2(X36,X37),X37)
        | r1_xboole_0(X36,X37) )
      & ( ~ r2_hidden(X41,X39)
        | ~ r2_hidden(X41,X40)
        | ~ r1_xboole_0(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(esk6_3(X17,X18,X19),X19),X17)
        | X18 != k2_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X22,X21),X17)
        | r2_hidden(X21,X18)
        | X18 != k2_relat_1(X17) )
      & ( ~ r2_hidden(esk7_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(X26,esk7_2(X23,X24)),X23)
        | X24 = k2_relat_1(X23) )
      & ( r2_hidden(esk7_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk8_2(X23,X24),esk7_2(X23,X24)),X23)
        | X24 = k2_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( X2 = k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X30,X31] :
      ( ~ r1_xboole_0(X30,X31)
      | r1_xboole_0(X31,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_15,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(esk3_2(esk2_0,X1),esk4_2(esk2_0,X1)) = X1
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(esk3_2(esk2_0,esk10_2(esk1_0,esk2_0)),esk4_2(esk2_0,esk10_2(esk1_0,esk2_0))) = esk10_2(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_2(esk2_0,esk10_2(esk1_0,esk2_0)),k2_relat_1(X1))
    | ~ r2_hidden(esk10_2(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk10_2(esk1_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk1_0))
    | ~ r2_hidden(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_2(esk2_0,esk10_2(esk1_0,esk2_0)),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_2(esk2_0,esk10_2(esk1_0,esk2_0)),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
