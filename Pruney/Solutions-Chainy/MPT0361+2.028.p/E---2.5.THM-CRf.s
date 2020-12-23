%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:22 EST 2020

% Result     : Theorem 44.23s
% Output     : CNFRefutation 44.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 357 expanded)
%              Number of clauses        :   61 ( 181 expanded)
%              Number of leaves         :   10 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  219 (1669 expanded)
%              Number of equality atoms :   41 ( 350 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_10,plain,(
    ! [X36] : ~ v1_xboole_0(k1_zfmisc_1(X36)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_11,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X33,X32)
        | r2_hidden(X33,X32)
        | v1_xboole_0(X32) )
      & ( ~ r2_hidden(X33,X32)
        | m1_subset_1(X33,X32)
        | v1_xboole_0(X32) )
      & ( ~ m1_subset_1(X33,X32)
        | v1_xboole_0(X33)
        | ~ v1_xboole_0(X32) )
      & ( ~ v1_xboole_0(X33)
        | m1_subset_1(X33,X32)
        | ~ v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

fof(c_0_13,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | r1_tarski(X27,X25)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r1_tarski(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r2_hidden(esk3_2(X29,X30),X30)
        | ~ r1_tarski(esk3_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | r1_tarski(esk3_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ~ r1_tarski(k3_subset_1(esk4_0,k4_subset_1(esk4_0,esk5_0,esk6_0)),k3_subset_1(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_35,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

fof(c_0_46,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | k3_subset_1(X34,X35) = k4_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_38])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk4_0)
    | r2_hidden(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk6_0,X1) = X1
    | r2_hidden(esk2_3(esk6_0,X1,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_55,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_tarski(k4_xboole_0(X22,X21),k4_xboole_0(X22,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_56,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(k2_xboole_0(X1,esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_32])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(esk6_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_53]),c_0_53])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_54])).

fof(c_0_62,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | k4_subset_1(X37,X38,X39) = k2_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k3_subset_1(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(X1,X2) = esk4_0
    | ~ r2_hidden(esk2_3(X1,X2,esk4_0),esk6_0)
    | ~ r2_hidden(esk2_3(X1,X2,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( X1 = k2_xboole_0(k2_xboole_0(X2,X3),X4)
    | r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X4)
    | r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X1)
    | r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X3)
    | r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_27])).

cnf(c_0_68,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_subset_1(k2_xboole_0(X1,X2),X1),k4_xboole_0(k2_xboole_0(X1,X2),X3))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,esk4_0),esk5_0) = k3_subset_1(k2_xboole_0(X1,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k2_xboole_0(X1,esk4_0) = esk4_0
    | ~ r2_hidden(esk2_3(X1,esk4_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_45])).

cnf(c_0_72,negated_conjecture,
    ( X1 = k2_xboole_0(k2_xboole_0(esk5_0,X2),X3)
    | r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),esk4_0)
    | r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),X2)
    | r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),X1)
    | r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k4_subset_1(esk4_0,X1,esk6_0) = k2_xboole_0(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k3_subset_1(k2_xboole_0(X1,esk4_0),X1),k3_subset_1(k2_xboole_0(X1,esk4_0),esk5_0))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0) = esk4_0
    | r2_hidden(esk2_3(k2_xboole_0(esk5_0,esk6_0),esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,k4_subset_1(esk4_0,esk5_0,esk6_0)),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_77,negated_conjecture,
    ( k4_subset_1(esk4_0,esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_19])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k3_subset_1(k2_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0),k2_xboole_0(esk5_0,X1)),k3_subset_1(k2_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_75]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k3_subset_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 44.23/44.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 44.23/44.46  # and selection function SelectCQIArNXTEqFirst.
% 44.23/44.46  #
% 44.23/44.46  # Preprocessing time       : 0.028 s
% 44.23/44.46  # Presaturation interreduction done
% 44.23/44.46  
% 44.23/44.46  # Proof found!
% 44.23/44.46  # SZS status Theorem
% 44.23/44.46  # SZS output start CNFRefutation
% 44.23/44.46  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 44.23/44.46  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 44.23/44.46  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 44.23/44.46  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 44.23/44.46  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 44.23/44.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 44.23/44.46  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 44.23/44.46  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 44.23/44.46  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 44.23/44.46  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 44.23/44.46  fof(c_0_10, plain, ![X36]:~v1_xboole_0(k1_zfmisc_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 44.23/44.46  fof(c_0_11, plain, ![X32, X33]:(((~m1_subset_1(X33,X32)|r2_hidden(X33,X32)|v1_xboole_0(X32))&(~r2_hidden(X33,X32)|m1_subset_1(X33,X32)|v1_xboole_0(X32)))&((~m1_subset_1(X33,X32)|v1_xboole_0(X33)|~v1_xboole_0(X32))&(~v1_xboole_0(X33)|m1_subset_1(X33,X32)|~v1_xboole_0(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 44.23/44.46  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 44.23/44.46  fof(c_0_13, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|r1_tarski(X27,X25)|X26!=k1_zfmisc_1(X25))&(~r1_tarski(X28,X25)|r2_hidden(X28,X26)|X26!=k1_zfmisc_1(X25)))&((~r2_hidden(esk3_2(X29,X30),X30)|~r1_tarski(esk3_2(X29,X30),X29)|X30=k1_zfmisc_1(X29))&(r2_hidden(esk3_2(X29,X30),X30)|r1_tarski(esk3_2(X29,X30),X29)|X30=k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 44.23/44.46  cnf(c_0_14, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 44.23/44.46  cnf(c_0_15, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 44.23/44.46  fof(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))&~r1_tarski(k3_subset_1(esk4_0,k4_subset_1(esk4_0,esk5_0,esk6_0)),k3_subset_1(esk4_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 44.23/44.46  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 44.23/44.46  cnf(c_0_18, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 44.23/44.46  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 44.23/44.46  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 44.23/44.46  fof(c_0_21, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 44.23/44.46  fof(c_0_22, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 44.23/44.46  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 44.23/44.46  cnf(c_0_24, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 44.23/44.46  cnf(c_0_25, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 44.23/44.46  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 44.23/44.46  cnf(c_0_27, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.23/44.46  fof(c_0_28, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 44.23/44.46  cnf(c_0_29, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.23/44.46  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 44.23/44.46  cnf(c_0_31, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 44.23/44.46  cnf(c_0_32, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_25])).
% 44.23/44.46  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 44.23/44.46  cnf(c_0_34, negated_conjecture, (r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 44.23/44.46  cnf(c_0_35, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.23/44.46  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_27])).
% 44.23/44.46  cnf(c_0_37, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 44.23/44.46  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 44.23/44.46  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 44.23/44.46  cnf(c_0_40, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_29])).
% 44.23/44.46  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 44.23/44.46  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 44.23/44.46  cnf(c_0_43, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.23/44.46  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_34])).
% 44.23/44.46  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 44.23/44.46  fof(c_0_46, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|k3_subset_1(X34,X35)=k4_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 44.23/44.46  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_37])).
% 44.23/44.46  cnf(c_0_48, plain, (r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_32, c_0_38])).
% 44.23/44.46  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 44.23/44.46  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk4_0)|r2_hidden(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 44.23/44.46  cnf(c_0_51, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.23/44.46  cnf(c_0_52, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_43])).
% 44.23/44.46  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk6_0,X1)=X1|r2_hidden(esk2_3(esk6_0,X1,X1),esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 44.23/44.46  cnf(c_0_54, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.23/44.46  fof(c_0_55, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_tarski(k4_xboole_0(X22,X21),k4_xboole_0(X22,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 44.23/44.46  cnf(c_0_56, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 44.23/44.46  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 44.23/44.46  cnf(c_0_58, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(k2_xboole_0(X1,esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_32])).
% 44.23/44.46  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X3)|~r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 44.23/44.46  cnf(c_0_60, negated_conjecture, (k2_xboole_0(esk6_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_53]), c_0_53])).
% 44.23/44.46  cnf(c_0_61, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_54])).
% 44.23/44.46  fof(c_0_62, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|~m1_subset_1(X39,k1_zfmisc_1(X37))|k4_subset_1(X37,X38,X39)=k2_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 44.23/44.46  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 44.23/44.46  cnf(c_0_64, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k3_subset_1(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 44.23/44.46  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_47, c_0_58])).
% 44.23/44.46  cnf(c_0_66, negated_conjecture, (k2_xboole_0(X1,X2)=esk4_0|~r2_hidden(esk2_3(X1,X2,esk4_0),esk6_0)|~r2_hidden(esk2_3(X1,X2,esk4_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 44.23/44.46  cnf(c_0_67, plain, (X1=k2_xboole_0(k2_xboole_0(X2,X3),X4)|r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X4)|r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X1)|r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X3)|r2_hidden(esk2_3(k2_xboole_0(X2,X3),X4,X1),X2)), inference(spm,[status(thm)],[c_0_61, c_0_27])).
% 44.23/44.46  cnf(c_0_68, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 44.23/44.46  cnf(c_0_69, plain, (r1_tarski(k3_subset_1(k2_xboole_0(X1,X2),X1),k4_xboole_0(k2_xboole_0(X1,X2),X3))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 44.23/44.46  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,esk4_0),esk5_0)=k3_subset_1(k2_xboole_0(X1,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_65])).
% 44.23/44.46  cnf(c_0_71, negated_conjecture, (k2_xboole_0(X1,esk4_0)=esk4_0|~r2_hidden(esk2_3(X1,esk4_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_45])).
% 44.23/44.46  cnf(c_0_72, negated_conjecture, (X1=k2_xboole_0(k2_xboole_0(esk5_0,X2),X3)|r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),esk4_0)|r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),X2)|r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),X1)|r2_hidden(esk2_3(k2_xboole_0(esk5_0,X2),X3,X1),X3)), inference(spm,[status(thm)],[c_0_41, c_0_67])).
% 44.23/44.46  cnf(c_0_73, negated_conjecture, (k4_subset_1(esk4_0,X1,esk6_0)=k2_xboole_0(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_68, c_0_20])).
% 44.23/44.46  cnf(c_0_74, negated_conjecture, (r1_tarski(k3_subset_1(k2_xboole_0(X1,esk4_0),X1),k3_subset_1(k2_xboole_0(X1,esk4_0),esk5_0))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 44.23/44.46  cnf(c_0_75, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)=esk4_0|r2_hidden(esk2_3(k2_xboole_0(esk5_0,esk6_0),esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 44.23/44.46  cnf(c_0_76, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,k4_subset_1(esk4_0,esk5_0,esk6_0)),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 44.23/44.46  cnf(c_0_77, negated_conjecture, (k4_subset_1(esk4_0,esk5_0,esk6_0)=k2_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_73, c_0_19])).
% 44.23/44.46  cnf(c_0_78, negated_conjecture, (r1_tarski(k3_subset_1(k2_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0),k2_xboole_0(esk5_0,X1)),k3_subset_1(k2_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_38])).
% 44.23/44.46  cnf(c_0_79, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_75]), c_0_75])).
% 44.23/44.46  cnf(c_0_80, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k3_subset_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 44.23/44.46  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), ['proof']).
% 44.23/44.46  # SZS output end CNFRefutation
% 44.23/44.46  # Proof object total steps             : 82
% 44.23/44.46  # Proof object clause steps            : 61
% 44.23/44.46  # Proof object formula steps           : 21
% 44.23/44.46  # Proof object conjectures             : 29
% 44.23/44.46  # Proof object clause conjectures      : 26
% 44.23/44.46  # Proof object formula conjectures     : 3
% 44.23/44.46  # Proof object initial clauses used    : 21
% 44.23/44.46  # Proof object initial formulas used   : 10
% 44.23/44.46  # Proof object generating inferences   : 34
% 44.23/44.46  # Proof object simplifying inferences  : 11
% 44.23/44.46  # Training examples: 0 positive, 0 negative
% 44.23/44.46  # Parsed axioms                        : 10
% 44.23/44.46  # Removed by relevancy pruning/SinE    : 0
% 44.23/44.46  # Initial clauses                      : 25
% 44.23/44.46  # Removed in clause preprocessing      : 0
% 44.23/44.46  # Initial clauses in saturation        : 25
% 44.23/44.46  # Processed clauses                    : 33824
% 44.23/44.46  # ...of these trivial                  : 379
% 44.23/44.46  # ...subsumed                          : 19820
% 44.23/44.46  # ...remaining for further processing  : 13625
% 44.23/44.46  # Other redundant clauses eliminated   : 5
% 44.23/44.46  # Clauses deleted for lack of memory   : 238487
% 44.23/44.46  # Backward-subsumed                    : 706
% 44.23/44.46  # Backward-rewritten                   : 504
% 44.23/44.46  # Generated clauses                    : 4092943
% 44.23/44.46  # ...of the previous two non-trivial   : 4018002
% 44.23/44.46  # Contextual simplify-reflections      : 200
% 44.23/44.46  # Paramodulations                      : 4089518
% 44.23/44.46  # Factorizations                       : 3420
% 44.23/44.46  # Equation resolutions                 : 5
% 44.23/44.46  # Propositional unsat checks           : 0
% 44.23/44.46  #    Propositional check models        : 0
% 44.23/44.46  #    Propositional check unsatisfiable : 0
% 44.23/44.46  #    Propositional clauses             : 0
% 44.23/44.46  #    Propositional clauses after purity: 0
% 44.23/44.46  #    Propositional unsat core size     : 0
% 44.23/44.46  #    Propositional preprocessing time  : 0.000
% 44.23/44.46  #    Propositional encoding time       : 0.000
% 44.23/44.46  #    Propositional solver time         : 0.000
% 44.23/44.46  #    Success case prop preproc time    : 0.000
% 44.23/44.46  #    Success case prop encoding time   : 0.000
% 44.23/44.46  #    Success case prop solver time     : 0.000
% 44.23/44.46  # Current number of processed clauses  : 12385
% 44.23/44.46  #    Positive orientable unit clauses  : 832
% 44.23/44.46  #    Positive unorientable unit clauses: 0
% 44.23/44.46  #    Negative unit clauses             : 2
% 44.23/44.46  #    Non-unit-clauses                  : 11551
% 44.23/44.46  # Current number of unprocessed clauses: 1791717
% 44.23/44.46  # ...number of literals in the above   : 8875193
% 44.23/44.46  # Current number of archived formulas  : 0
% 44.23/44.46  # Current number of archived clauses   : 1235
% 44.23/44.46  # Clause-clause subsumption calls (NU) : 40583293
% 44.23/44.46  # Rec. Clause-clause subsumption calls : 7449544
% 44.23/44.46  # Non-unit clause-clause subsumptions  : 19964
% 44.23/44.46  # Unit Clause-clause subsumption calls : 466782
% 44.23/44.46  # Rewrite failures with RHS unbound    : 0
% 44.23/44.46  # BW rewrite match attempts            : 11412
% 44.23/44.46  # BW rewrite match successes           : 146
% 44.23/44.46  # Condensation attempts                : 0
% 44.23/44.46  # Condensation successes               : 0
% 44.23/44.46  # Termbank termtop insertions          : 132031189
% 44.31/44.54  
% 44.31/44.54  # -------------------------------------------------
% 44.31/44.54  # User time                : 43.138 s
% 44.31/44.54  # System time              : 1.023 s
% 44.31/44.54  # Total time               : 44.161 s
% 44.31/44.54  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
