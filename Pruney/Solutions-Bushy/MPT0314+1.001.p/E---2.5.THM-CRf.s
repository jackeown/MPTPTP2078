%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0314+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:24 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 600 expanded)
%              Number of clauses        :   43 ( 325 expanded)
%              Number of leaves         :   11 ( 157 expanded)
%              Depth                    :   16
%              Number of atoms          :  111 (1675 expanded)
%              Number of equality atoms :   58 ( 643 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(t126_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
    ! [X29] :
      ( ~ v1_xboole_0(X29)
      | X29 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_13,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_17,plain,(
    ! [X22,X23,X24] :
      ( k2_zfmisc_1(k4_xboole_0(X22,X23),X24) = k4_xboole_0(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X24))
      & k2_zfmisc_1(X24,k4_xboole_0(X22,X23)) = k4_xboole_0(k2_zfmisc_1(X24,X22),k2_zfmisc_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_20])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X1),X2) = k2_zfmisc_1(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k4_xboole_0(X3,X4)))
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X1,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k4_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),X2) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_34,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k4_xboole_0(X3,X4)),X5))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X4),X5)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),k4_xboole_0(X2,X2)) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_28])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3),X4)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_39])).

fof(c_0_41,plain,(
    ! [X25] : k2_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_42,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_43,plain,(
    ! [X26,X27,X28] : k4_xboole_0(X26,k3_xboole_0(X27,X28)) = k2_xboole_0(k4_xboole_0(X26,X27),k4_xboole_0(X26,X28)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    inference(assume_negation,[status(cth)],[t126_zfmisc_1])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_14])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X18,X19,X20,X21] : k2_zfmisc_1(k3_xboole_0(X18,X19),k3_xboole_0(X20,X21)) = k3_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X21)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_50,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_52,negated_conjecture,(
    k4_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,esk5_0)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(esk2_0,esk4_0),esk3_0),k2_zfmisc_1(esk2_0,k4_xboole_0(esk3_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k4_xboole_0(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(X3,k2_zfmisc_1(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,esk5_0)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(esk2_0,esk4_0),esk3_0),k2_zfmisc_1(esk2_0,k4_xboole_0(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_53]),c_0_54])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_55])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X4,X2))) = k2_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk2_0,k4_xboole_0(esk3_0,esk5_0)),k2_zfmisc_1(k4_xboole_0(esk2_0,esk4_0),esk3_0)) != k4_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),
    [proof]).

%------------------------------------------------------------------------------
