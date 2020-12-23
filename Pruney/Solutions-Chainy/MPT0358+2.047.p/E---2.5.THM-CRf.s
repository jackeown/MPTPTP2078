%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:56 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   88 (10492 expanded)
%              Number of clauses        :   65 (5200 expanded)
%              Number of leaves         :   11 (2546 expanded)
%              Depth                    :   25
%              Number of atoms          :  215 (36439 expanded)
%              Number of equality atoms :   52 (8330 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

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

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_11,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | r1_tarski(X28,X26)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r1_tarski(X29,X26)
        | r2_hidden(X29,X27)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r2_hidden(esk4_2(X30,X31),X31)
        | ~ r1_tarski(esk4_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | r1_tarski(esk4_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ( ~ m1_subset_1(X34,X33)
        | r2_hidden(X34,X33)
        | v1_xboole_0(X33) )
      & ( ~ r2_hidden(X34,X33)
        | m1_subset_1(X34,X33)
        | v1_xboole_0(X33) )
      & ( ~ m1_subset_1(X34,X33)
        | v1_xboole_0(X34)
        | ~ v1_xboole_0(X33) )
      & ( ~ v1_xboole_0(X34)
        | m1_subset_1(X34,X33)
        | ~ v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 != k1_subset_1(esk5_0) )
    & ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 = k1_subset_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X38] : ~ v1_xboole_0(k1_zfmisc_1(X38)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_20,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k3_subset_1(X36,X37) = k4_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_21,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])).

fof(c_0_33,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_37,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_41,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_43])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k3_subset_1(esk6_0,esk6_0)
    | r2_hidden(esk2_3(esk6_0,esk5_0,X1),esk6_0)
    | r2_hidden(esk2_3(esk6_0,esk5_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk1_2(X1,X2),k3_subset_1(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_45]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k3_subset_1(esk6_0,esk6_0) = esk6_0
    | r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_51]),c_0_48]),c_0_48]),c_0_48])])).

fof(c_0_54,plain,(
    ! [X35] : k1_subset_1(X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)
    | r2_hidden(esk6_0,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 != k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_58,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk3_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk6_0,X1) = esk6_0
    | r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)
    | ~ r2_hidden(X1,k3_subset_1(esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | r2_hidden(esk3_1(X1),X1)
    | ~ r1_tarski(X1,k3_subset_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 = k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_57])).

cnf(c_0_71,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k1_xboole_0)
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0)) = k3_subset_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_69]),c_0_76])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_77,c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_78])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_45]),c_0_49])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_subset_1(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_45]),c_0_49])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk3_1(k3_subset_1(k1_xboole_0,k1_xboole_0)),k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_61]),c_0_78])])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk3_1(k3_subset_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(esk3_1(k3_subset_1(k1_xboole_0,k1_xboole_0)),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_45]),c_0_49]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:03:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.85/1.06  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.85/1.06  # and selection function SelectCQIArEqFirst.
% 0.85/1.06  #
% 0.85/1.06  # Preprocessing time       : 0.028 s
% 0.85/1.06  # Presaturation interreduction done
% 0.85/1.06  
% 0.85/1.06  # Proof found!
% 0.85/1.06  # SZS status Theorem
% 0.85/1.06  # SZS output start CNFRefutation
% 0.85/1.06  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.85/1.06  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.85/1.06  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.85/1.06  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.85/1.06  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.85/1.06  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.85/1.06  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.85/1.06  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.85/1.06  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.85/1.06  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.85/1.06  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.85/1.06  fof(c_0_11, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|r1_tarski(X28,X26)|X27!=k1_zfmisc_1(X26))&(~r1_tarski(X29,X26)|r2_hidden(X29,X27)|X27!=k1_zfmisc_1(X26)))&((~r2_hidden(esk4_2(X30,X31),X31)|~r1_tarski(esk4_2(X30,X31),X30)|X31=k1_zfmisc_1(X30))&(r2_hidden(esk4_2(X30,X31),X31)|r1_tarski(esk4_2(X30,X31),X30)|X31=k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.85/1.06  cnf(c_0_12, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.85/1.06  fof(c_0_13, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.85/1.06  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.85/1.06  cnf(c_0_15, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_12])).
% 0.85/1.06  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.85/1.06  fof(c_0_17, plain, ![X33, X34]:(((~m1_subset_1(X34,X33)|r2_hidden(X34,X33)|v1_xboole_0(X33))&(~r2_hidden(X34,X33)|m1_subset_1(X34,X33)|v1_xboole_0(X33)))&((~m1_subset_1(X34,X33)|v1_xboole_0(X34)|~v1_xboole_0(X33))&(~v1_xboole_0(X34)|m1_subset_1(X34,X33)|~v1_xboole_0(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.85/1.06  fof(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&((~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0))&(r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.85/1.06  fof(c_0_19, plain, ![X38]:~v1_xboole_0(k1_zfmisc_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.85/1.06  fof(c_0_20, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k3_subset_1(X36,X37)=k4_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.85/1.06  fof(c_0_21, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.85/1.06  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.85/1.06  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.85/1.06  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.85/1.06  fof(c_0_25, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.85/1.06  cnf(c_0_26, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.85/1.06  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.85/1.06  cnf(c_0_28, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.85/1.06  cnf(c_0_29, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.85/1.06  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.85/1.06  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.85/1.06  cnf(c_0_32, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])).
% 0.85/1.06  fof(c_0_33, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.85/1.06  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_24])).
% 0.85/1.06  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.85/1.06  cnf(c_0_36, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.85/1.06  cnf(c_0_37, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.85/1.06  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_28])).
% 0.85/1.06  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.85/1.06  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.85/1.06  cnf(c_0_41, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_30])).
% 0.85/1.06  cnf(c_0_42, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.85/1.06  cnf(c_0_43, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.85/1.06  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.85/1.06  cnf(c_0_45, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.85/1.06  cnf(c_0_46, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_41])).
% 0.85/1.06  cnf(c_0_47, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_42, c_0_30])).
% 0.85/1.06  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk6_0), inference(spm,[status(thm)],[c_0_39, c_0_43])).
% 0.85/1.06  cnf(c_0_49, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.85/1.06  cnf(c_0_50, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.85/1.06  cnf(c_0_51, negated_conjecture, (X1=k3_subset_1(esk6_0,esk6_0)|r2_hidden(esk2_3(esk6_0,esk5_0,X1),esk6_0)|r2_hidden(esk2_3(esk6_0,esk5_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.85/1.06  cnf(c_0_52, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(esk1_2(X1,X2),k3_subset_1(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_45]), c_0_49])).
% 0.85/1.06  cnf(c_0_53, negated_conjecture, (k3_subset_1(esk6_0,esk6_0)=esk6_0|r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_51]), c_0_48]), c_0_48]), c_0_48])])).
% 0.85/1.06  fof(c_0_54, plain, ![X35]:k1_subset_1(X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.85/1.06  cnf(c_0_55, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)|r2_hidden(esk6_0,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_23])).
% 0.85/1.06  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.85/1.06  cnf(c_0_57, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.85/1.06  fof(c_0_58, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk3_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.85/1.06  cnf(c_0_59, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_55])).
% 0.85/1.06  cnf(c_0_60, negated_conjecture, (esk6_0!=k1_xboole_0|~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.85/1.06  cnf(c_0_61, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.85/1.06  cnf(c_0_62, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1))))), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.85/1.06  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk6_0,X1)=esk6_0|r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_59])).
% 0.85/1.06  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|~r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.85/1.06  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)|~r2_hidden(X1,k3_subset_1(esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_49])).
% 0.85/1.06  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|r2_hidden(esk3_1(X1),X1)|~r1_tarski(X1,k3_subset_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_64, c_0_61])).
% 0.85/1.06  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_53])).
% 0.85/1.06  cnf(c_0_68, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.85/1.06  cnf(c_0_69, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_59]), c_0_67])).
% 0.85/1.06  cnf(c_0_70, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_68, c_0_57])).
% 0.85/1.06  cnf(c_0_71, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.85/1.06  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k1_xboole_0)|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.85/1.06  cnf(c_0_73, negated_conjecture, (~r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_46, c_0_69])).
% 0.85/1.06  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0))=k3_subset_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.85/1.06  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k1_xboole_0)|r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.85/1.06  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk2_3(esk6_0,esk5_0,esk6_0),k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.85/1.06  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.85/1.06  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_69]), c_0_76])).
% 0.85/1.06  cnf(c_0_79, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_77, c_0_30])).
% 0.85/1.06  cnf(c_0_80, negated_conjecture, (~r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_46, c_0_78])).
% 0.85/1.06  cnf(c_0_81, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_79])).
% 0.85/1.06  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),k3_subset_1(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_45]), c_0_49])).
% 0.85/1.06  cnf(c_0_83, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_subset_1(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_45]), c_0_49])).
% 0.85/1.06  cnf(c_0_84, negated_conjecture, (r2_hidden(esk3_1(k3_subset_1(k1_xboole_0,k1_xboole_0)),k3_subset_1(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_61]), c_0_78])])).
% 0.85/1.06  cnf(c_0_85, negated_conjecture, (r2_hidden(esk3_1(k3_subset_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.85/1.06  cnf(c_0_86, negated_conjecture, (~r2_hidden(esk3_1(k3_subset_1(k1_xboole_0,k1_xboole_0)),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_46, c_0_85])).
% 0.85/1.06  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_45]), c_0_49]), c_0_84])]), ['proof']).
% 0.85/1.06  # SZS output end CNFRefutation
% 0.85/1.06  # Proof object total steps             : 88
% 0.85/1.06  # Proof object clause steps            : 65
% 0.85/1.06  # Proof object formula steps           : 23
% 0.85/1.06  # Proof object conjectures             : 33
% 0.85/1.06  # Proof object clause conjectures      : 30
% 0.85/1.06  # Proof object formula conjectures     : 3
% 0.85/1.06  # Proof object initial clauses used    : 19
% 0.85/1.06  # Proof object initial formulas used   : 11
% 0.85/1.06  # Proof object generating inferences   : 35
% 0.85/1.06  # Proof object simplifying inferences  : 31
% 0.85/1.06  # Training examples: 0 positive, 0 negative
% 0.85/1.06  # Parsed axioms                        : 11
% 0.85/1.06  # Removed by relevancy pruning/SinE    : 0
% 0.85/1.06  # Initial clauses                      : 26
% 0.85/1.06  # Removed in clause preprocessing      : 2
% 0.85/1.06  # Initial clauses in saturation        : 24
% 0.85/1.06  # Processed clauses                    : 2164
% 0.85/1.06  # ...of these trivial                  : 18
% 0.85/1.06  # ...subsumed                          : 1107
% 0.85/1.06  # ...remaining for further processing  : 1039
% 0.85/1.06  # Other redundant clauses eliminated   : 16
% 0.85/1.06  # Clauses deleted for lack of memory   : 0
% 0.85/1.06  # Backward-subsumed                    : 66
% 0.85/1.06  # Backward-rewritten                   : 118
% 0.85/1.06  # Generated clauses                    : 64399
% 0.85/1.06  # ...of the previous two non-trivial   : 63493
% 0.85/1.06  # Contextual simplify-reflections      : 11
% 0.85/1.06  # Paramodulations                      : 64377
% 0.85/1.06  # Factorizations                       : 6
% 0.85/1.06  # Equation resolutions                 : 16
% 0.85/1.06  # Propositional unsat checks           : 0
% 0.85/1.06  #    Propositional check models        : 0
% 0.85/1.06  #    Propositional check unsatisfiable : 0
% 0.85/1.06  #    Propositional clauses             : 0
% 0.85/1.06  #    Propositional clauses after purity: 0
% 0.85/1.06  #    Propositional unsat core size     : 0
% 0.85/1.06  #    Propositional preprocessing time  : 0.000
% 0.85/1.06  #    Propositional encoding time       : 0.000
% 0.85/1.06  #    Propositional solver time         : 0.000
% 0.85/1.06  #    Success case prop preproc time    : 0.000
% 0.85/1.06  #    Success case prop encoding time   : 0.000
% 0.85/1.06  #    Success case prop solver time     : 0.000
% 0.85/1.06  # Current number of processed clauses  : 826
% 0.85/1.06  #    Positive orientable unit clauses  : 36
% 0.85/1.06  #    Positive unorientable unit clauses: 0
% 0.85/1.06  #    Negative unit clauses             : 30
% 0.85/1.06  #    Non-unit-clauses                  : 760
% 0.85/1.06  # Current number of unprocessed clauses: 60813
% 0.85/1.06  # ...number of literals in the above   : 322178
% 0.85/1.06  # Current number of archived formulas  : 0
% 0.85/1.06  # Current number of archived clauses   : 210
% 0.85/1.06  # Clause-clause subsumption calls (NU) : 128606
% 0.85/1.06  # Rec. Clause-clause subsumption calls : 76807
% 0.85/1.06  # Non-unit clause-clause subsumptions  : 1103
% 0.85/1.06  # Unit Clause-clause subsumption calls : 4874
% 0.85/1.06  # Rewrite failures with RHS unbound    : 0
% 0.85/1.06  # BW rewrite match attempts            : 135
% 0.85/1.06  # BW rewrite match successes           : 33
% 0.85/1.06  # Condensation attempts                : 0
% 0.85/1.06  # Condensation successes               : 0
% 0.85/1.06  # Termbank termtop insertions          : 1270934
% 0.85/1.06  
% 0.85/1.06  # -------------------------------------------------
% 0.85/1.06  # User time                : 0.687 s
% 0.85/1.06  # System time              : 0.032 s
% 0.85/1.06  # Total time               : 0.719 s
% 0.85/1.06  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
