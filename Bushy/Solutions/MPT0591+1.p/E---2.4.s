%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t195_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:57 EDT 2019

% Result     : Theorem 265.54s
% Output     : CNFRefutation 265.54s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 340 expanded)
%              Number of clauses        :   48 ( 177 expanded)
%              Number of leaves         :    7 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  168 (1279 expanded)
%              Number of equality atoms :   71 ( 349 expanded)
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
    file('/export/starexec/sandbox/benchmark/relat_1__t195_relat_1.p',t106_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t195_relat_1.p',d4_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t195_relat_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t195_relat_1.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t195_relat_1.p',t6_boole)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t195_relat_1.p',d5_relat_1)).

fof(t195_relat_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t195_relat_1.p',t195_relat_1)).

fof(c_0_7,plain,(
    ! [X37,X38,X39,X40] :
      ( ( r2_hidden(X37,X39)
        | ~ r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) )
      & ( r2_hidden(X38,X40)
        | ~ r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) )
      & ( ~ r2_hidden(X37,X39)
        | ~ r2_hidden(X38,X40)
        | r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk4_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk5_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk5_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk5_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk5_2(X19,X20),esk6_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_12,plain,(
    ! [X35] : m1_subset_1(esk10_1(X35),X35) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_13,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X45] :
      ( ~ v1_xboole_0(X45)
      | X45 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | r2_hidden(esk5_2(k2_zfmisc_1(X1,X2),X1),X1) ),
    inference(ef,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_21,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(esk7_3(X24,X25,X26),X26),X24)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(esk8_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk8_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) )
      & ( r2_hidden(esk8_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk9_2(X30,X31),esk8_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_relat_1(k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_14])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk10_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ r2_hidden(k4_tarski(esk5_2(k2_zfmisc_1(X1,X2),X1),X3),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk10_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X3 != k1_relat_1(k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(esk5_2(k2_zfmisc_1(X1,X2),X1),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_27]),c_0_19])).

cnf(c_0_35,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk8_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk8_2(k2_zfmisc_1(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | r2_hidden(esk10_1(k1_relat_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ r2_hidden(esk5_2(k2_zfmisc_1(X1,X2),X1),k1_relat_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_39,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X3 != k1_relat_1(X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_14])).

cnf(c_0_40,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_relat_1(k2_zfmisc_1(X3,X4))
    | r2_hidden(esk5_2(k2_zfmisc_1(X3,X4),k1_relat_1(k2_zfmisc_1(X1,X2))),X3)
    | r2_hidden(esk5_2(k2_zfmisc_1(X3,X4),k1_relat_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_13])).

cnf(c_0_41,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk8_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk8_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | r2_hidden(esk8_2(k2_zfmisc_1(X1,X2),X2),X2) ),
    inference(ef,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(X3,X1)) = X3 ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_44,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X2 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19])).

cnf(c_0_45,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ r2_hidden(X3,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_relat_1(k2_zfmisc_1(X1,X3))
    | r2_hidden(esk5_2(k2_zfmisc_1(X1,X3),k1_relat_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(ef,[status(thm)],[c_0_40])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
              & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t195_relat_1])).

cnf(c_0_48,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | ~ r2_hidden(k4_tarski(X3,esk8_2(k2_zfmisc_1(X1,X2),X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X1)) = X1 ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_43]),c_0_44])).

cnf(c_0_50,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X1),X2)) = k1_relat_1(k2_zfmisc_1(k1_relat_1(X1),X3))
    | k1_relat_1(k2_zfmisc_1(X4,X1)) = X4 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_51,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & ( k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk1_0
      | k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).

cnf(c_0_52,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_42])).

cnf(c_0_53,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X1),X2)) = k1_relat_1(X1)
    | k1_relat_1(k2_zfmisc_1(X3,X1)) = X3 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk1_0
    | k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_55,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | k2_relat_1(k2_zfmisc_1(X1,X3)) = X3 ),
    inference(spm,[status(thm)],[c_0_52,c_0_36])).

cnf(c_0_56,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X1),X1)) = k1_relat_1(X1) ),
    inference(ef,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk1_0,X1)) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,k2_zfmisc_1(X1,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk1_0,X1)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
