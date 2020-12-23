%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:17 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   89 (1011 expanded)
%              Number of clauses        :   60 ( 443 expanded)
%              Number of leaves         :   14 ( 278 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 (1237 expanded)
%              Number of equality atoms :   81 (1003 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_14,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X24,X25] : k2_xboole_0(X24,X25) = k5_xboole_0(X24,k4_xboole_0(X25,X24)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X20] : k2_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_18,plain,(
    ! [X23] : k4_xboole_0(k1_xboole_0,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_19,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_22])).

fof(c_0_31,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k3_subset_1(X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_34])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_30]),c_0_34])).

cnf(c_0_41,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_22])).

fof(c_0_42,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | k4_subset_1(X33,X34,X35) = k2_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | m1_subset_1(k3_subset_1(X29,X30),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,k3_subset_1(X31,X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_45])).

cnf(c_0_54,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_28])).

fof(c_0_57,plain,(
    ! [X26] : k2_subset_1(X26) = X26 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_58,plain,
    ( k4_subset_1(X2,X1,X3) = k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_21]),c_0_22])).

cnf(c_0_59,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)) = k3_subset_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_62,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_53])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X1,X2,k3_xboole_0(X4,X3)),k3_xboole_0(X4,X3))
    | r2_hidden(esk1_3(X1,X2,k3_xboole_0(X4,X3)),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_54])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_68,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0))) = k4_subset_1(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)))) = k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_60])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_61,c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_51])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_65]),c_0_65]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) = k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_28]),c_0_71])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_70]),c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))) = k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_60]),c_0_28])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk2_0,k1_xboole_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_34]),c_0_81])).

cnf(c_0_85,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_82,c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk2_0,k1_xboole_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_28]),c_0_66])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_87]),c_0_34]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:54:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.41/0.60  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.41/0.60  # and selection function SelectNegativeLiterals.
% 0.41/0.60  #
% 0.41/0.60  # Preprocessing time       : 0.027 s
% 0.41/0.60  # Presaturation interreduction done
% 0.41/0.60  
% 0.41/0.60  # Proof found!
% 0.41/0.60  # SZS status Theorem
% 0.41/0.60  # SZS output start CNFRefutation
% 0.41/0.60  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.41/0.60  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.41/0.60  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.41/0.60  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.41/0.60  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.41/0.60  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.41/0.60  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.41/0.60  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.41/0.60  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.41/0.60  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.41/0.60  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.41/0.60  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.41/0.60  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.41/0.60  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.41/0.60  fof(c_0_14, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.41/0.60  fof(c_0_15, plain, ![X24, X25]:k2_xboole_0(X24,X25)=k5_xboole_0(X24,k4_xboole_0(X25,X24)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.41/0.60  fof(c_0_16, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.41/0.60  fof(c_0_17, plain, ![X20]:k2_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.41/0.60  fof(c_0_18, plain, ![X23]:k4_xboole_0(k1_xboole_0,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.41/0.60  fof(c_0_19, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.41/0.60  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.41/0.60  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.41/0.60  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.60  fof(c_0_23, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.41/0.60  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.60  cnf(c_0_25, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.60  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.60  cnf(c_0_27, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.41/0.60  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.41/0.60  cnf(c_0_29, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_22])).
% 0.41/0.60  cnf(c_0_30, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_22])).
% 0.41/0.60  fof(c_0_31, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.41/0.60  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22])).
% 0.41/0.60  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.41/0.60  cnf(c_0_34, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.41/0.60  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.60  fof(c_0_36, plain, ![X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k3_subset_1(X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.41/0.60  fof(c_0_37, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.41/0.60  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_32, c_0_28])).
% 0.41/0.60  cnf(c_0_39, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_34])).
% 0.41/0.60  cnf(c_0_40, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_30]), c_0_34])).
% 0.41/0.60  cnf(c_0_41, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_22])).
% 0.41/0.60  fof(c_0_42, plain, ![X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|~m1_subset_1(X35,k1_zfmisc_1(X33))|k4_subset_1(X33,X34,X35)=k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.41/0.60  cnf(c_0_43, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.41/0.60  fof(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.41/0.60  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.41/0.60  cnf(c_0_46, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.60  cnf(c_0_47, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_41])).
% 0.41/0.60  cnf(c_0_48, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.41/0.60  fof(c_0_49, plain, ![X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X29))|m1_subset_1(k3_subset_1(X29,X30),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.41/0.60  cnf(c_0_50, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_22])).
% 0.41/0.60  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.41/0.60  fof(c_0_52, plain, ![X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k3_subset_1(X31,k3_subset_1(X31,X32))=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.41/0.60  cnf(c_0_53, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[c_0_40, c_0_45])).
% 0.41/0.60  cnf(c_0_54, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_46, c_0_22])).
% 0.41/0.60  cnf(c_0_55, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.41/0.60  cnf(c_0_56, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_28])).
% 0.41/0.60  fof(c_0_57, plain, ![X26]:k2_subset_1(X26)=X26, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.41/0.60  cnf(c_0_58, plain, (k4_subset_1(X2,X1,X3)=k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_21]), c_0_22])).
% 0.41/0.60  cnf(c_0_59, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.41/0.60  cnf(c_0_60, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))=k3_subset_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.41/0.60  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.60  cnf(c_0_62, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.41/0.60  cnf(c_0_63, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_53])).
% 0.41/0.60  cnf(c_0_64, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X3,X4)|r2_hidden(esk1_3(X1,X2,k3_xboole_0(X4,X3)),k3_xboole_0(X4,X3))|r2_hidden(esk1_3(X1,X2,k3_xboole_0(X4,X3)),X1)), inference(spm,[status(thm)],[c_0_28, c_0_54])).
% 0.41/0.60  cnf(c_0_65, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_55, c_0_53])).
% 0.41/0.60  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_30])).
% 0.41/0.60  cnf(c_0_67, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.41/0.60  cnf(c_0_68, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.41/0.60  cnf(c_0_69, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))=k4_subset_1(esk2_0,esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_58, c_0_51])).
% 0.41/0.60  cnf(c_0_70, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_51])).
% 0.41/0.60  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))))=k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_60])).
% 0.41/0.60  cnf(c_0_72, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_61, c_0_22])).
% 0.41/0.60  cnf(c_0_73, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_62, c_0_51])).
% 0.41/0.60  cnf(c_0_74, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_65]), c_0_65]), c_0_66])).
% 0.41/0.60  cnf(c_0_75, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.41/0.60  cnf(c_0_76, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))=k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_28]), c_0_71])).
% 0.41/0.60  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_72])).
% 0.41/0.60  cnf(c_0_78, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_70]), c_0_73])).
% 0.41/0.60  cnf(c_0_79, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))=k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_60]), c_0_28])).
% 0.41/0.60  cnf(c_0_80, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_74, c_0_28])).
% 0.41/0.60  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.41/0.60  cnf(c_0_82, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.60  cnf(c_0_83, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.41/0.60  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk2_0,k1_xboole_0),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_34]), c_0_81])).
% 0.41/0.60  cnf(c_0_85, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_82, c_0_22])).
% 0.41/0.60  cnf(c_0_86, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk2_0,k1_xboole_0),esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.41/0.60  cnf(c_0_87, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_28]), c_0_66])).
% 0.41/0.60  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_87]), c_0_34]), c_0_81]), ['proof']).
% 0.41/0.60  # SZS output end CNFRefutation
% 0.41/0.60  # Proof object total steps             : 89
% 0.41/0.60  # Proof object clause steps            : 60
% 0.41/0.60  # Proof object formula steps           : 29
% 0.41/0.60  # Proof object conjectures             : 20
% 0.41/0.60  # Proof object clause conjectures      : 17
% 0.41/0.60  # Proof object formula conjectures     : 3
% 0.41/0.60  # Proof object initial clauses used    : 18
% 0.41/0.60  # Proof object initial formulas used   : 14
% 0.41/0.60  # Proof object generating inferences   : 22
% 0.41/0.60  # Proof object simplifying inferences  : 46
% 0.41/0.60  # Training examples: 0 positive, 0 negative
% 0.41/0.60  # Parsed axioms                        : 14
% 0.41/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.60  # Initial clauses                      : 20
% 0.41/0.60  # Removed in clause preprocessing      : 3
% 0.41/0.60  # Initial clauses in saturation        : 17
% 0.41/0.60  # Processed clauses                    : 1074
% 0.41/0.60  # ...of these trivial                  : 143
% 0.41/0.60  # ...subsumed                          : 553
% 0.41/0.60  # ...remaining for further processing  : 378
% 0.41/0.60  # Other redundant clauses eliminated   : 218
% 0.41/0.60  # Clauses deleted for lack of memory   : 0
% 0.41/0.60  # Backward-subsumed                    : 6
% 0.41/0.60  # Backward-rewritten                   : 83
% 0.41/0.60  # Generated clauses                    : 21401
% 0.41/0.60  # ...of the previous two non-trivial   : 16987
% 0.41/0.60  # Contextual simplify-reflections      : 14
% 0.41/0.60  # Paramodulations                      : 21183
% 0.41/0.60  # Factorizations                       : 0
% 0.41/0.60  # Equation resolutions                 : 218
% 0.41/0.60  # Propositional unsat checks           : 0
% 0.41/0.60  #    Propositional check models        : 0
% 0.41/0.60  #    Propositional check unsatisfiable : 0
% 0.41/0.60  #    Propositional clauses             : 0
% 0.41/0.60  #    Propositional clauses after purity: 0
% 0.41/0.60  #    Propositional unsat core size     : 0
% 0.41/0.60  #    Propositional preprocessing time  : 0.000
% 0.41/0.60  #    Propositional encoding time       : 0.000
% 0.41/0.60  #    Propositional solver time         : 0.000
% 0.41/0.60  #    Success case prop preproc time    : 0.000
% 0.41/0.60  #    Success case prop encoding time   : 0.000
% 0.41/0.60  #    Success case prop solver time     : 0.000
% 0.41/0.60  # Current number of processed clauses  : 269
% 0.41/0.60  #    Positive orientable unit clauses  : 35
% 0.41/0.60  #    Positive unorientable unit clauses: 3
% 0.41/0.60  #    Negative unit clauses             : 4
% 0.41/0.60  #    Non-unit-clauses                  : 227
% 0.41/0.60  # Current number of unprocessed clauses: 15675
% 0.41/0.60  # ...number of literals in the above   : 68429
% 0.41/0.60  # Current number of archived formulas  : 0
% 0.41/0.60  # Current number of archived clauses   : 109
% 0.41/0.60  # Clause-clause subsumption calls (NU) : 8454
% 0.41/0.60  # Rec. Clause-clause subsumption calls : 7137
% 0.41/0.60  # Non-unit clause-clause subsumptions  : 481
% 0.41/0.60  # Unit Clause-clause subsumption calls : 787
% 0.41/0.60  # Rewrite failures with RHS unbound    : 0
% 0.41/0.60  # BW rewrite match attempts            : 81
% 0.41/0.60  # BW rewrite match successes           : 38
% 0.41/0.60  # Condensation attempts                : 0
% 0.41/0.60  # Condensation successes               : 0
% 0.41/0.60  # Termbank termtop insertions          : 441123
% 0.41/0.60  
% 0.41/0.60  # -------------------------------------------------
% 0.41/0.60  # User time                : 0.237 s
% 0.41/0.60  # System time              : 0.008 s
% 0.41/0.60  # Total time               : 0.245 s
% 0.41/0.60  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
