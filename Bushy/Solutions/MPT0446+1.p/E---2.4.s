%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t30_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  51 expanded)
%              Number of clauses        :   20 (  24 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 187 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',t30_relat_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d3_xboole_0)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d6_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d4_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
         => ( r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_relat_1])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X14)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk4_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk4_3(X17,X18,X19),X18)
        | ~ r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k2_xboole_0(X17,X18) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X19)
        | r2_hidden(esk4_3(X17,X18,X19),X17)
        | r2_hidden(esk4_3(X17,X18,X19),X18)
        | X19 = k2_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X43] :
      ( ~ v1_relat_1(X43)
      | k3_relat_1(X43) = k2_xboole_0(k1_relat_1(X43),k2_relat_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
    & ( ~ r2_hidden(esk1_0,k3_relat_1(esk3_0))
      | ~ r2_hidden(esk2_0,k3_relat_1(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( ~ r2_hidden(X34,X33)
        | r2_hidden(k4_tarski(esk8_3(X32,X33,X34),X34),X32)
        | X33 != k2_relat_1(X32) )
      & ( ~ r2_hidden(k4_tarski(X37,X36),X32)
        | r2_hidden(X36,X33)
        | X33 != k2_relat_1(X32) )
      & ( ~ r2_hidden(esk9_2(X38,X39),X39)
        | ~ r2_hidden(k4_tarski(X41,esk9_2(X38,X39)),X38)
        | X39 = k2_relat_1(X38) )
      & ( r2_hidden(esk9_2(X38,X39),X39)
        | r2_hidden(k4_tarski(esk10_2(X38,X39),esk9_2(X38,X39)),X38)
        | X39 = k2_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X25,X26,X27,X28,X30] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(k4_tarski(X23,esk5_3(X21,X22,X23)),X21)
        | X22 != k1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X25,X26),X21)
        | r2_hidden(X25,X22)
        | X22 != k1_relat_1(X21) )
      & ( ~ r2_hidden(esk6_2(X27,X28),X28)
        | ~ r2_hidden(k4_tarski(esk6_2(X27,X28),X30),X27)
        | X28 = k1_relat_1(X27) )
      & ( r2_hidden(esk6_2(X27,X28),X28)
        | r2_hidden(k4_tarski(esk6_2(X27,X28),esk7_2(X27,X28)),X27)
        | X28 = k1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk3_0),k2_relat_1(esk3_0)) = k3_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk3_0))
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k3_relat_1(esk3_0))
    | ~ r2_hidden(esk2_0,k3_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_0,k3_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk3_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
