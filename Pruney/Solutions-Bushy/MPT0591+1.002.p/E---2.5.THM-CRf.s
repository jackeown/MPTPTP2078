%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0591+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:52 EST 2020

% Result     : Theorem 40.09s
% Output     : CNFRefutation 40.09s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 299 expanded)
%              Number of clauses        :   41 ( 151 expanded)
%              Number of leaves         :    7 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 (1115 expanded)
%              Number of equality atoms :   61 ( 324 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t195_relat_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(c_0_7,plain,(
    ! [X29,X30,X31,X32] :
      ( ( r2_hidden(X29,X31)
        | ~ r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)) )
      & ( r2_hidden(X30,X32)
        | ~ r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)) )
      & ( ~ r2_hidden(X29,X31)
        | ~ r2_hidden(X30,X32)
        | r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)
        | X12 = k1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)
        | X12 = k1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_13,plain,(
    ! [X27] : m1_subset_1(esk7_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_14,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X18),X16)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(esk5_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) )
      & ( r2_hidden(esk5_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),X1),X1) ),
    inference(ef,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_18])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
              & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t195_relat_1])).

cnf(c_0_28,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X35] :
      ( ~ v1_xboole_0(X35)
      | X35 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_30,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_relat_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(esk7_1(k1_relat_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & ( k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0
      | k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_33,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | r2_hidden(esk5_2(k2_zfmisc_1(X1,X2),X2),X2) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | v1_xboole_0(k1_relat_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0
    | k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | k1_relat_1(k2_zfmisc_1(X3,X2)) = X3 ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_38,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_39,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(X3,X1)) = X3 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(X1,esk9_0)) = X1
    | k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | k1_xboole_0 = X2
    | v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(X1,esk9_0)) = X1
    | v1_xboole_0(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(X1,esk9_0)) = X1
    | X2 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,esk9_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_44])])).

cnf(c_0_46,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk5_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(X1,esk9_0)) = X1
    | k1_relat_1(k2_zfmisc_1(X2,esk9_0)) = X2 ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_48,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(X1,esk9_0)) = X1 ),
    inference(ef,[status(thm)],[c_0_47])).

cnf(c_0_50,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_49])])).

cnf(c_0_52,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_53]),c_0_54]),
    [proof]).

%------------------------------------------------------------------------------
