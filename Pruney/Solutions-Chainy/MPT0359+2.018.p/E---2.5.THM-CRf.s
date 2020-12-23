%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 559 expanded)
%              Number of clauses        :   65 ( 272 expanded)
%              Number of leaves         :   12 ( 139 expanded)
%              Depth                    :   15
%              Number of atoms          :  234 (1739 expanded)
%              Number of equality atoms :   61 ( 442 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t39_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X21)
        | X22 = k4_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X21)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_13,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_20,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_21,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | k3_subset_1(X38,X39) = k4_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(k3_subset_1(X1,X2),X2)
        <=> X2 = k2_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t39_subset_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1)
    | r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
      | esk5_0 != k2_subset_1(esk4_0) )
    & ( r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
      | esk5_0 = k2_subset_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_34,plain,(
    ! [X37] : k2_subset_1(X37) = X37 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_38,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
    | esk5_0 = k2_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_37])])).

fof(c_0_44,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk3_2(X32,X33),X33)
        | ~ r1_tarski(esk3_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk3_2(X32,X33),X33)
        | r1_tarski(esk3_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k3_subset_1(X2,X1))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 = esk4_0
    | r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_27])).

cnf(c_0_50,plain,
    ( X1 = k5_xboole_0(X2,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_51,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X40] : ~ v1_xboole_0(k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_15])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk1_2(k3_subset_1(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk1_2(k3_subset_1(esk4_0,esk5_0),X1),esk5_0)
    | r1_tarski(k3_subset_1(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_43])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_tarski(k3_subset_1(esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_35])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_37])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
    | esk5_0 != k2_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_57]),c_0_62])).

fof(c_0_73,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k3_subset_1(X2,X3))
    | r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( k3_subset_1(esk4_0,esk5_0) = k5_xboole_0(X1,X1)
    | esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_66])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_59]),c_0_37])]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 != esk4_0
    | ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_41])).

cnf(c_0_78,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_82,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_57])]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 != esk5_0
    | ~ r1_tarski(k5_xboole_0(esk5_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])]),c_0_80])).

cnf(c_0_84,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_35])).

cnf(c_0_85,negated_conjecture,
    ( esk4_0 = esk5_0
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk1_2(esk4_0,X1),esk5_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_86]),c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.036 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.47  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.47  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.47  fof(t39_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 0.20/0.47  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.47  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.47  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.47  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.47  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.20/0.47  fof(c_0_12, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k4_xboole_0(X15,X16)))&((~r2_hidden(esk2_3(X20,X21,X22),X22)|(~r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X21))|X22=k4_xboole_0(X20,X21))&((r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))&(~r2_hidden(esk2_3(X20,X21,X22),X21)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.47  fof(c_0_13, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.47  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_17, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.47  fof(c_0_18, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.47  cnf(c_0_19, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.20/0.47  fof(c_0_20, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.47  fof(c_0_21, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.47  cnf(c_0_22, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.47  fof(c_0_25, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|k3_subset_1(X38,X39)=k4_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.47  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1)))), inference(assume_negation,[status(cth)],[t39_subset_1])).
% 0.20/0.47  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_29, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.47  cnf(c_0_30, plain, (r2_hidden(esk1_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1)|r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.20/0.47  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_32, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.47  fof(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0!=k2_subset_1(esk4_0))&(r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0=k2_subset_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.20/0.47  fof(c_0_34, plain, ![X37]:k2_subset_1(X37)=X37, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.47  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.47  cnf(c_0_36, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.47  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.20/0.47  cnf(c_0_38, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_32, c_0_15])).
% 0.20/0.47  cnf(c_0_39, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0=k2_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.47  cnf(c_0_41, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.47  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 0.20/0.47  cnf(c_0_43, plain, (r1_tarski(k5_xboole_0(X1,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_37])])).
% 0.20/0.47  fof(c_0_44, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk3_2(X32,X33),X33)|~r1_tarski(esk3_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk3_2(X32,X33),X33)|r1_tarski(esk3_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.47  cnf(c_0_45, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_46, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k3_subset_1(X2,X1))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_22, c_0_38])).
% 0.20/0.47  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_23])).
% 0.20/0.47  cnf(c_0_48, negated_conjecture, (esk5_0=esk4_0|r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.47  cnf(c_0_49, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_27])).
% 0.20/0.47  cnf(c_0_50, plain, (X1=k5_xboole_0(X2,X2)|~r1_tarski(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.47  fof(c_0_51, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.47  cnf(c_0_52, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.47  fof(c_0_53, plain, ![X40]:~v1_xboole_0(k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.47  cnf(c_0_54, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_15])).
% 0.20/0.47  cnf(c_0_55, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(esk1_2(k3_subset_1(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk1_2(k3_subset_1(esk4_0,esk5_0),X1),esk5_0)|r1_tarski(k3_subset_1(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.47  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.47  cnf(c_0_58, plain, (~r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_49, c_0_28])).
% 0.20/0.47  cnf(c_0_59, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_50, c_0_43])).
% 0.20/0.47  cnf(c_0_60, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.47  cnf(c_0_61, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.47  cnf(c_0_62, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.47  cnf(c_0_63, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.47  cnf(c_0_64, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.47  cnf(c_0_65, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_54])).
% 0.20/0.47  cnf(c_0_66, negated_conjecture, (esk4_0=esk5_0|r1_tarski(k3_subset_1(esk4_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.20/0.47  cnf(c_0_67, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_35])).
% 0.20/0.47  cnf(c_0_68, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_37])])).
% 0.20/0.47  cnf(c_0_69, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0!=k2_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.47  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.20/0.47  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_63])).
% 0.20/0.47  cnf(c_0_72, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_57]), c_0_62])).
% 0.20/0.47  fof(c_0_73, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k5_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.20/0.47  cnf(c_0_74, plain, (r2_hidden(X1,k3_subset_1(X2,X3))|r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_65, c_0_38])).
% 0.20/0.47  cnf(c_0_75, negated_conjecture, (k3_subset_1(esk4_0,esk5_0)=k5_xboole_0(X1,X1)|esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_50, c_0_66])).
% 0.20/0.47  cnf(c_0_76, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_59]), c_0_37])]), c_0_68])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, (esk5_0!=esk4_0|~r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_69, c_0_41])).
% 0.20/0.47  cnf(c_0_78, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_70])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.47  cnf(c_0_80, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.47  cnf(c_0_81, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.20/0.47  cnf(c_0_82, negated_conjecture, (esk4_0=esk5_0|r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_57])]), c_0_76])).
% 0.20/0.47  cnf(c_0_83, negated_conjecture, (esk4_0!=esk5_0|~r1_tarski(k5_xboole_0(esk5_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])]), c_0_80])).
% 0.20/0.47  cnf(c_0_84, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_81, c_0_35])).
% 0.20/0.47  cnf(c_0_85, negated_conjecture, (esk4_0=esk5_0|~r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_79])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk1_2(esk4_0,X1),esk5_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_23])).
% 0.20/0.47  cnf(c_0_87, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.20/0.47  cnf(c_0_88, negated_conjecture, (esk4_0=esk5_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_86]), c_0_87])).
% 0.20/0.47  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_37])]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 90
% 0.20/0.47  # Proof object clause steps            : 65
% 0.20/0.47  # Proof object formula steps           : 25
% 0.20/0.47  # Proof object conjectures             : 20
% 0.20/0.47  # Proof object clause conjectures      : 17
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 20
% 0.20/0.47  # Proof object initial formulas used   : 12
% 0.20/0.47  # Proof object generating inferences   : 33
% 0.20/0.47  # Proof object simplifying inferences  : 34
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 12
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 27
% 0.20/0.47  # Removed in clause preprocessing      : 2
% 0.20/0.47  # Initial clauses in saturation        : 25
% 0.20/0.47  # Processed clauses                    : 717
% 0.20/0.47  # ...of these trivial                  : 4
% 0.20/0.47  # ...subsumed                          : 482
% 0.20/0.47  # ...remaining for further processing  : 231
% 0.20/0.47  # Other redundant clauses eliminated   : 5
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 12
% 0.20/0.47  # Backward-rewritten                   : 65
% 0.20/0.47  # Generated clauses                    : 2719
% 0.20/0.47  # ...of the previous two non-trivial   : 2553
% 0.20/0.47  # Contextual simplify-reflections      : 18
% 0.20/0.47  # Paramodulations                      : 2710
% 0.20/0.47  # Factorizations                       : 4
% 0.20/0.47  # Equation resolutions                 : 5
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 124
% 0.20/0.47  #    Positive orientable unit clauses  : 6
% 0.20/0.47  #    Positive unorientable unit clauses: 3
% 0.20/0.47  #    Negative unit clauses             : 2
% 0.20/0.47  #    Non-unit-clauses                  : 113
% 0.20/0.47  # Current number of unprocessed clauses: 1874
% 0.20/0.47  # ...number of literals in the above   : 7229
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 104
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 8593
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 5458
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 443
% 0.20/0.47  # Unit Clause-clause subsumption calls : 95
% 0.20/0.47  # Rewrite failures with RHS unbound    : 48
% 0.20/0.47  # BW rewrite match attempts            : 65
% 0.20/0.47  # BW rewrite match successes           : 12
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 44389
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.127 s
% 0.20/0.47  # System time              : 0.006 s
% 0.20/0.47  # Total time               : 0.133 s
% 0.20/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
