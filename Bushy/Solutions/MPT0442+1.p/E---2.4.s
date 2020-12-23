%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t25_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:00 EDT 2019

% Result     : Theorem 18.26s
% Output     : CNFRefutation 18.26s
% Verified   : 
% Statistics : Number of formulae       :   49 (  95 expanded)
%              Number of clauses        :   34 (  47 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 345 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t25_relat_1.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t25_relat_1.p',d4_relat_1)).

fof(t25_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t25_relat_1.p',t25_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t25_relat_1.p',d3_tarski)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t25_relat_1.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t25_relat_1.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t25_relat_1.p',t1_subset)).

fof(c_0_7,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( ~ r2_hidden(X28,X27)
        | r2_hidden(k4_tarski(esk7_3(X26,X27,X28),X28),X26)
        | X27 != k2_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X31,X30),X26)
        | r2_hidden(X30,X27)
        | X27 != k2_relat_1(X26) )
      & ( ~ r2_hidden(esk8_2(X32,X33),X33)
        | ~ r2_hidden(k4_tarski(X35,esk8_2(X32,X33)),X32)
        | X33 = k2_relat_1(X32) )
      & ( r2_hidden(esk8_2(X32,X33),X33)
        | r2_hidden(k4_tarski(esk9_2(X32,X33),esk8_2(X32,X33)),X32)
        | X33 = k2_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(X17,esk4_3(X15,X16,X17)),X15)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X15)
        | r2_hidden(X19,X16)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(esk5_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(esk5_2(X21,X22),X24),X21)
        | X22 = k1_relat_1(X21) )
      & ( r2_hidden(esk5_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk5_2(X21,X22),esk6_2(X21,X22)),X21)
        | X22 = k1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
                & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_relat_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk3_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk3_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,esk2_0)
    & ( ~ r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk2_0))
      | ~ r1_tarski(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X52,X53)
      | ~ v1_xboole_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_3(X1,k1_relat_1(X1),X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_3(esk1_0,k2_relat_1(esk1_0),X1),X1),esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X41,X42)
      | v1_xboole_0(X42)
      | r2_hidden(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk1_0))
    | ~ r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk2_0))
    | ~ r2_hidden(X1,k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_28])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_35,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | m1_subset_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk2_0))
    | ~ m1_subset_1(X1,k2_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_3(esk1_0,k1_relat_1(esk1_0),X1)),esk2_0)
    | ~ r2_hidden(X1,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk2_0))
    | ~ m1_subset_1(esk3_2(X1,k2_relat_1(esk2_0)),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_2(k1_relat_1(esk1_0),X1),k1_relat_1(esk2_0))
    | r1_tarski(k1_relat_1(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
