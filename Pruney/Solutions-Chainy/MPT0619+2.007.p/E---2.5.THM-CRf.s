%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:51 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 369 expanded)
%              Number of clauses        :   39 ( 148 expanded)
%              Number of leaves         :   13 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 696 expanded)
%              Number of equality atoms :   66 ( 412 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(k1_tarski(X14),X15)
      | ~ r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k1_relat_1(esk3_0) = k1_tarski(esk2_0)
    & k2_relat_1(esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | k11_relat_1(X19,X20) = k9_relat_1(X19,k1_tarski(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_20,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ( r2_hidden(esk1_2(X16,X17),X16)
        | X16 = k1_tarski(X17)
        | X16 = k1_xboole_0 )
      & ( esk1_2(X16,X17) != X17
        | X16 = k1_tarski(X17)
        | X16 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

cnf(c_0_26,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk3_0) = k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_22]),c_0_23])).

fof(c_0_29,plain,(
    ! [X22,X23] :
      ( ( k9_relat_1(X23,X22) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X23),X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_xboole_0(k1_relat_1(X23),X22)
        | k9_relat_1(X23,X22) = k1_xboole_0
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ( ~ r1_tarski(k1_tarski(X12),X13)
        | r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X12,X13)
        | r1_tarski(k1_tarski(X12),X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_31,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k9_relat_1(X21,k1_relat_1(X21)) = k2_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_35,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk3_0),X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk3_0) != k2_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_43,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k9_relat_1(X1,k1_relat_1(esk3_0)) = k11_relat_1(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) != k1_xboole_0
    | ~ r2_hidden(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(esk3_0) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(esk3_0) = k11_relat_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38])])).

cnf(c_0_50,negated_conjecture,
    ( k11_relat_1(esk3_0,X1) != k1_xboole_0
    | ~ r2_hidden(esk2_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_35]),c_0_38])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_52,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(k4_tarski(X24,X25),X26)
        | r2_hidden(X25,k11_relat_1(X26,X24))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X25,k11_relat_1(X26,X24))
        | r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_53,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)),k11_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_55,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X28 = k1_funct_1(X29,X27)
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X27,k1_relat_1(X29))
        | X28 != k1_funct_1(X29,X27)
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)),k11_relat_1(esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_38])])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) = k1_funct_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_38])])).

cnf(c_0_64,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) != k11_relat_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.13/0.38  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.13/0.38  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.13/0.38  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.13/0.38  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.13/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X14, X15]:(~r1_xboole_0(k1_tarski(X14),X15)|~r2_hidden(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.13/0.38  fof(c_0_15, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_16, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_17, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(k1_relat_1(esk3_0)=k1_tarski(esk2_0)&k2_relat_1(esk3_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X19, X20]:(~v1_relat_1(X19)|k11_relat_1(X19,X20)=k9_relat_1(X19,k1_tarski(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.13/0.38  cnf(c_0_20, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k1_relat_1(esk3_0)=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_25, plain, ![X16, X17]:((r2_hidden(esk1_2(X16,X17),X16)|(X16=k1_tarski(X17)|X16=k1_xboole_0))&(esk1_2(X16,X17)!=X17|(X16=k1_tarski(X17)|X16=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.13/0.38  cnf(c_0_26, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk3_0)=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  fof(c_0_29, plain, ![X22, X23]:((k9_relat_1(X23,X22)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X23),X22)|~v1_relat_1(X23))&(~r1_xboole_0(k1_relat_1(X23),X22)|k9_relat_1(X23,X22)=k1_xboole_0|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.13/0.38  fof(c_0_30, plain, ![X12, X13]:((~r1_tarski(k1_tarski(X12),X13)|r2_hidden(X12,X13))&(~r2_hidden(X12,X13)|r1_tarski(k1_tarski(X12),X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.38  fof(c_0_31, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk3_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  fof(c_0_34, plain, ![X21]:(~v1_relat_1(X21)|k9_relat_1(X21,k1_relat_1(X21))=k2_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.38  cnf(c_0_35, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk3_0),X1)|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_37, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk3_0)!=k2_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_42, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_43, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k9_relat_1(X1,k1_relat_1(esk3_0))=k11_relat_1(X1,esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (k9_relat_1(esk3_0,X1)!=k1_xboole_0|~r2_hidden(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.13/0.38  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k2_relat_1(esk3_0)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k2_relat_1(esk3_0)=k11_relat_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_38])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k11_relat_1(esk3_0,X1)!=k1_xboole_0|~r2_hidden(esk2_0,k2_enumset1(X1,X1,X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_35]), c_0_38])])).
% 0.13/0.38  cnf(c_0_51, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  fof(c_0_52, plain, ![X24, X25, X26]:((~r2_hidden(k4_tarski(X24,X25),X26)|r2_hidden(X25,k11_relat_1(X26,X24))|~v1_relat_1(X26))&(~r2_hidden(X25,k11_relat_1(X26,X24))|r2_hidden(k4_tarski(X24,X25),X26)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)=k1_xboole_0|r2_hidden(esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)),k11_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49]), c_0_49])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.38  fof(c_0_55, plain, ![X27, X28, X29]:(((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X28=k1_funct_1(X29,X27)|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X27,k1_relat_1(X29))|X28!=k1_funct_1(X29,X27)|r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.38  cnf(c_0_56, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)),k11_relat_1(esk3_0,esk2_0))), inference(sr,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.38  cnf(c_0_58, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_59, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_38])])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_62, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))=k1_funct_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_38])])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k2_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))!=k11_relat_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_41, c_0_49])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_54]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 66
% 0.13/0.38  # Proof object clause steps            : 39
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 22
% 0.13/0.38  # Proof object clause conjectures      : 19
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 41
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 89
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 12
% 0.13/0.38  # ...remaining for further processing  : 75
% 0.13/0.38  # Other redundant clauses eliminated   : 10
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 346
% 0.13/0.38  # ...of the previous two non-trivial   : 310
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 328
% 0.13/0.38  # Factorizations                       : 7
% 0.13/0.38  # Equation resolutions                 : 10
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 65
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 53
% 0.13/0.38  # Current number of unprocessed clauses: 241
% 0.13/0.38  # ...number of literals in the above   : 1477
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 10
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 263
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 139
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.13/0.38  # Unit Clause-clause subsumption calls : 13
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6588
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.043 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
