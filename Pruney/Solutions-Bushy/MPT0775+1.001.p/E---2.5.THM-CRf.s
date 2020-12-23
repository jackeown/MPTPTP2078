%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0775+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 150 expanded)
%              Number of clauses        :   37 (  66 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  164 ( 563 expanded)
%              Number of equality atoms :   13 (  55 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t24_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v8_relat_2(X2)
       => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ v8_relat_2(X18)
        | ~ r2_hidden(k4_tarski(X19,X20),X18)
        | ~ r2_hidden(k4_tarski(X20,X21),X18)
        | r2_hidden(k4_tarski(X19,X21),X18)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_1(X18),esk3_1(X18)),X18)
        | v8_relat_2(X18)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk3_1(X18),esk4_1(X18)),X18)
        | v8_relat_2(X18)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X18),esk4_1(X18)),X18)
        | v8_relat_2(X18)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

fof(c_0_8,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k2_wellord1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v8_relat_2(X2)
         => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t24_wellord1])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k2_wellord1(X14,X15) = k3_xboole_0(X14,k2_zfmisc_1(X15,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk3_1(X1),esk4_1(X1)),X1)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v8_relat_2(esk6_0)
    & ~ v8_relat_2(k2_wellord1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v8_relat_2(k2_wellord1(X1,X2))
    | r2_hidden(k4_tarski(esk3_1(k2_wellord1(X1,X2)),esk4_1(k2_wellord1(X1,X2))),k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X25,X26,X27,X28] :
      ( ( r2_hidden(X25,X27)
        | ~ r2_hidden(k4_tarski(X25,X26),k2_zfmisc_1(X27,X28)) )
      & ( r2_hidden(X26,X28)
        | ~ r2_hidden(k4_tarski(X25,X26),k2_zfmisc_1(X27,X28)) )
      & ( ~ r2_hidden(X25,X27)
        | ~ r2_hidden(X26,X28)
        | r2_hidden(k4_tarski(X25,X26),k2_zfmisc_1(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_wellord1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(esk3_1(k2_wellord1(esk6_0,X1)),esk4_1(k2_wellord1(esk6_0,X1))),k2_wellord1(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( v8_relat_2(k2_wellord1(X1,X2))
    | r2_hidden(k4_tarski(esk2_1(k2_wellord1(X1,X2)),esk3_1(k2_wellord1(X1,X2))),k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_wellord1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(esk3_1(k2_wellord1(esk6_0,X1)),esk4_1(k2_wellord1(esk6_0,X1))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_19])])).

cnf(c_0_32,negated_conjecture,
    ( v8_relat_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(esk2_1(k2_wellord1(esk6_0,X1)),esk3_1(k2_wellord1(esk6_0,X1))),k2_wellord1(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_wellord1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_35,plain,
    ( v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk2_1(X1),esk4_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_wellord1(X3,X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(X2,esk4_1(k2_wellord1(esk6_0,X1))),esk6_0)
    | ~ r2_hidden(k4_tarski(X2,esk3_1(k2_wellord1(esk6_0,X1))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_19])])).

cnf(c_0_38,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(esk2_1(k2_wellord1(esk6_0,X1)),esk3_1(k2_wellord1(esk6_0,X1))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_33]),c_0_19])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(esk2_1(k2_wellord1(esk6_0,X1)),esk3_1(k2_wellord1(esk6_0,X1))),k2_zfmisc_1(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_19])])).

cnf(c_0_41,plain,
    ( v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk2_1(k2_wellord1(X1,X2)),esk4_1(k2_wellord1(X1,X2))),X1)
    | ~ r2_hidden(esk4_1(k2_wellord1(X1,X2)),X2)
    | ~ r2_hidden(esk2_1(k2_wellord1(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(esk2_1(k2_wellord1(esk6_0,X1)),esk4_1(k2_wellord1(esk6_0,X1))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(esk2_1(k2_wellord1(esk6_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | r2_hidden(k4_tarski(esk3_1(k2_wellord1(esk6_0,X1)),esk4_1(k2_wellord1(esk6_0,X1))),k2_zfmisc_1(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_19])])).

cnf(c_0_46,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1))
    | ~ r2_hidden(esk4_1(k2_wellord1(esk6_0,X1)),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_19])]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( ~ v8_relat_2(k2_wellord1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk6_0,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),
    [proof]).

%------------------------------------------------------------------------------
