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
% DateTime   : Thu Dec  3 10:46:14 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   97 (1890 expanded)
%              Number of clauses        :   70 ( 878 expanded)
%              Number of leaves         :   13 ( 469 expanded)
%              Depth                    :   21
%              Number of atoms          :  233 (5112 expanded)
%              Number of equality atoms :   39 (1057 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_13,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | r1_tarski(X25,X23)
        | X24 != k1_zfmisc_1(X23) )
      & ( ~ r1_tarski(X26,X23)
        | r2_hidden(X26,X24)
        | X24 != k1_zfmisc_1(X23) )
      & ( ~ r2_hidden(esk2_2(X27,X28),X28)
        | ~ r1_tarski(esk2_2(X27,X28),X27)
        | X28 = k1_zfmisc_1(X27) )
      & ( r2_hidden(esk2_2(X27,X28),X28)
        | r1_tarski(esk2_2(X27,X28),X27)
        | X28 = k1_zfmisc_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_15,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | k3_subset_1(X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_17,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X31,X30)
        | r2_hidden(X31,X30)
        | v1_xboole_0(X30) )
      & ( ~ r2_hidden(X31,X30)
        | m1_subset_1(X31,X30)
        | v1_xboole_0(X30) )
      & ( ~ m1_subset_1(X31,X30)
        | v1_xboole_0(X31)
        | ~ v1_xboole_0(X30) )
      & ( ~ v1_xboole_0(X31)
        | m1_subset_1(X31,X30)
        | ~ v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & r1_tarski(esk4_0,esk5_0)
    & r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0))
    & esk4_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_28,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_29,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X17)
      | ~ r1_tarski(X17,X16)
      | ~ r1_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_xboole_0(X20,k4_xboole_0(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0))
    | v1_xboole_0(k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_38])).

fof(c_0_46,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0))
    | m1_subset_1(X1,k1_zfmisc_1(esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_31])])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_44])).

fof(c_0_51,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_45]),c_0_38])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_52])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k3_subset_1(esk5_0,esk4_0) = esk5_0
    | ~ r1_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k3_subset_1(esk5_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_65])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_56])])).

cnf(c_0_69,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_45])).

fof(c_0_71,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k3_subset_1(X36,k3_subset_1(X36,X37)) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk5_0))
    | m1_subset_1(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_74,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k3_subset_1(esk5_0,k1_xboole_0) = esk5_0
    | m1_subset_1(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_72]),c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( k3_subset_1(esk5_0,esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_67]),c_0_56])])).

cnf(c_0_77,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77]),c_0_72])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_79]),c_0_52])])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_27])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r1_tarski(X1,k3_subset_1(X4,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k3_subset_1(X1,X1) = X1
    | m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_34]),c_0_35])])).

cnf(c_0_87,negated_conjecture,
    ( k3_subset_1(esk4_0,esk4_0) = esk4_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_31])])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_69])).

cnf(c_0_89,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X1,k3_subset_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_90,negated_conjecture,
    ( k3_subset_1(esk4_0,esk4_0) = esk4_0
    | k3_subset_1(esk4_0,esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_87]),c_0_42])])).

cnf(c_0_91,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( k3_subset_1(esk4_0,esk4_0) = esk4_0
    | ~ r1_xboole_0(esk4_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_87])).

cnf(c_0_93,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_91]),c_0_73])])).

cnf(c_0_94,negated_conjecture,
    ( k3_subset_1(esk4_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_64]),c_0_31]),c_0_65])])).

cnf(c_0_95,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_93]),c_0_91])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.42/0.60  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.42/0.60  #
% 0.42/0.60  # Preprocessing time       : 0.028 s
% 0.42/0.60  # Presaturation interreduction done
% 0.42/0.60  
% 0.42/0.60  # Proof found!
% 0.42/0.60  # SZS status Theorem
% 0.42/0.60  # SZS output start CNFRefutation
% 0.42/0.60  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.42/0.60  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.42/0.60  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.42/0.60  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.42/0.60  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.42/0.60  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.42/0.60  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.42/0.60  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.42/0.60  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.42/0.60  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.42/0.60  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.42/0.60  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.42/0.60  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.42/0.60  fof(c_0_13, plain, ![X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X25,X24)|r1_tarski(X25,X23)|X24!=k1_zfmisc_1(X23))&(~r1_tarski(X26,X23)|r2_hidden(X26,X24)|X24!=k1_zfmisc_1(X23)))&((~r2_hidden(esk2_2(X27,X28),X28)|~r1_tarski(esk2_2(X27,X28),X27)|X28=k1_zfmisc_1(X27))&(r2_hidden(esk2_2(X27,X28),X28)|r1_tarski(esk2_2(X27,X28),X27)|X28=k1_zfmisc_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.42/0.60  fof(c_0_14, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.42/0.60  fof(c_0_15, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.42/0.60  fof(c_0_16, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|k3_subset_1(X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.42/0.60  fof(c_0_17, plain, ![X30, X31]:(((~m1_subset_1(X31,X30)|r2_hidden(X31,X30)|v1_xboole_0(X30))&(~r2_hidden(X31,X30)|m1_subset_1(X31,X30)|v1_xboole_0(X30)))&((~m1_subset_1(X31,X30)|v1_xboole_0(X31)|~v1_xboole_0(X30))&(~v1_xboole_0(X31)|m1_subset_1(X31,X30)|~v1_xboole_0(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.42/0.60  cnf(c_0_18, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.60  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.42/0.60  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.42/0.60  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.60  cnf(c_0_22, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.60  cnf(c_0_23, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.60  cnf(c_0_24, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_18])).
% 0.42/0.60  fof(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&((r1_tarski(esk4_0,esk5_0)&r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0)))&esk4_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.42/0.60  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.42/0.60  cnf(c_0_27, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.42/0.60  fof(c_0_28, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.42/0.60  fof(c_0_29, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.42/0.60  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|v1_xboole_0(k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.42/0.60  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  fof(c_0_32, plain, ![X16, X17]:(v1_xboole_0(X17)|(~r1_tarski(X17,X16)|~r1_xboole_0(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.42/0.60  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.42/0.60  cnf(c_0_34, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  fof(c_0_36, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_xboole_0(X20,k4_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.42/0.60  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.42/0.60  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.42/0.60  cnf(c_0_39, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.60  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0))|v1_xboole_0(k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.42/0.60  cnf(c_0_41, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.42/0.60  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.42/0.60  cnf(c_0_43, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.42/0.60  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_21])).
% 0.42/0.60  cnf(c_0_45, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_38])).
% 0.42/0.60  fof(c_0_46, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.42/0.60  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0))|m1_subset_1(X1,k1_zfmisc_1(esk5_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.42/0.60  cnf(c_0_48, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_31])])).
% 0.42/0.60  cnf(c_0_49, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_21])).
% 0.42/0.60  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_44])).
% 0.42/0.60  fof(c_0_51, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.42/0.60  cnf(c_0_52, plain, (v1_xboole_0(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_45]), c_0_38])])).
% 0.42/0.60  cnf(c_0_53, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.60  cnf(c_0_54, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.42/0.60  cnf(c_0_55, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.42/0.60  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.42/0.60  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_49, c_0_44])).
% 0.42/0.60  cnf(c_0_58, negated_conjecture, (r1_xboole_0(X1,esk5_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 0.42/0.60  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.42/0.60  cnf(c_0_60, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.42/0.60  cnf(c_0_61, plain, (m1_subset_1(X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_52])).
% 0.42/0.60  cnf(c_0_62, plain, (v1_xboole_0(k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.60  cnf(c_0_63, negated_conjecture, (k3_subset_1(esk5_0,esk4_0)=esk5_0|~r1_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.42/0.60  cnf(c_0_64, negated_conjecture, (r1_xboole_0(X1,X2)|~r1_tarski(X1,esk5_0)|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.42/0.60  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.42/0.60  cnf(c_0_66, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.42/0.60  cnf(c_0_67, negated_conjecture, (k3_subset_1(esk5_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_65])])).
% 0.42/0.60  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk5_0,k1_xboole_0)|~v1_xboole_0(k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_56])])).
% 0.42/0.60  cnf(c_0_69, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 0.42/0.60  cnf(c_0_70, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_45])).
% 0.42/0.60  fof(c_0_71, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k3_subset_1(X36,k3_subset_1(X36,X37))=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.42/0.60  cnf(c_0_72, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk5_0))|m1_subset_1(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.42/0.60  cnf(c_0_73, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 0.42/0.60  cnf(c_0_74, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.42/0.60  cnf(c_0_75, negated_conjecture, (k3_subset_1(esk5_0,k1_xboole_0)=esk5_0|m1_subset_1(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_72]), c_0_73])])).
% 0.42/0.60  cnf(c_0_76, negated_conjecture, (k3_subset_1(esk5_0,esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_67]), c_0_56])])).
% 0.42/0.60  cnf(c_0_77, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  cnf(c_0_78, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_65])).
% 0.42/0.60  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77]), c_0_72])).
% 0.42/0.60  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_39, c_0_78])).
% 0.42/0.60  cnf(c_0_81, negated_conjecture, (v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_79]), c_0_52])])).
% 0.42/0.60  cnf(c_0_82, plain, (r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_49, c_0_27])).
% 0.42/0.60  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.42/0.60  cnf(c_0_84, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~r1_tarski(X1,k3_subset_1(X4,X3))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_57, c_0_82])).
% 0.42/0.60  cnf(c_0_85, negated_conjecture, (k3_subset_1(X1,X1)=X1|m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_55, c_0_83])).
% 0.42/0.60  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk4_0,X1)|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_34]), c_0_35])])).
% 0.42/0.60  cnf(c_0_87, negated_conjecture, (k3_subset_1(esk4_0,esk4_0)=esk4_0|m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_31])])).
% 0.42/0.60  cnf(c_0_88, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_39, c_0_69])).
% 0.42/0.60  cnf(c_0_89, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X1,k3_subset_1(X1,X2))), inference(spm,[status(thm)],[c_0_55, c_0_54])).
% 0.42/0.60  cnf(c_0_90, negated_conjecture, (k3_subset_1(esk4_0,esk4_0)=esk4_0|k3_subset_1(esk4_0,esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_87]), c_0_42])])).
% 0.42/0.60  cnf(c_0_91, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_88, c_0_52])).
% 0.42/0.60  cnf(c_0_92, negated_conjecture, (k3_subset_1(esk4_0,esk4_0)=esk4_0|~r1_xboole_0(esk4_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_87])).
% 0.42/0.60  cnf(c_0_93, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_91]), c_0_73])])).
% 0.42/0.60  cnf(c_0_94, negated_conjecture, (k3_subset_1(esk4_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_64]), c_0_31]), c_0_65])])).
% 0.42/0.60  cnf(c_0_95, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_93]), c_0_91])])).
% 0.42/0.60  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95]), c_0_77]), ['proof']).
% 0.42/0.60  # SZS output end CNFRefutation
% 0.42/0.60  # Proof object total steps             : 97
% 0.42/0.60  # Proof object clause steps            : 70
% 0.42/0.60  # Proof object formula steps           : 27
% 0.42/0.60  # Proof object conjectures             : 30
% 0.42/0.60  # Proof object clause conjectures      : 27
% 0.42/0.60  # Proof object formula conjectures     : 3
% 0.42/0.60  # Proof object initial clauses used    : 19
% 0.42/0.60  # Proof object initial formulas used   : 13
% 0.42/0.60  # Proof object generating inferences   : 45
% 0.42/0.60  # Proof object simplifying inferences  : 41
% 0.42/0.60  # Training examples: 0 positive, 0 negative
% 0.42/0.60  # Parsed axioms                        : 13
% 0.42/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.60  # Initial clauses                      : 26
% 0.42/0.60  # Removed in clause preprocessing      : 1
% 0.42/0.60  # Initial clauses in saturation        : 25
% 0.42/0.60  # Processed clauses                    : 2515
% 0.42/0.60  # ...of these trivial                  : 11
% 0.42/0.60  # ...subsumed                          : 1370
% 0.42/0.60  # ...remaining for further processing  : 1134
% 0.42/0.60  # Other redundant clauses eliminated   : 10
% 0.42/0.60  # Clauses deleted for lack of memory   : 0
% 0.42/0.60  # Backward-subsumed                    : 161
% 0.42/0.60  # Backward-rewritten                   : 280
% 0.42/0.60  # Generated clauses                    : 11243
% 0.42/0.60  # ...of the previous two non-trivial   : 9245
% 0.42/0.60  # Contextual simplify-reflections      : 66
% 0.42/0.60  # Paramodulations                      : 11223
% 0.42/0.60  # Factorizations                       : 10
% 0.42/0.60  # Equation resolutions                 : 10
% 0.42/0.60  # Propositional unsat checks           : 0
% 0.42/0.60  #    Propositional check models        : 0
% 0.42/0.60  #    Propositional check unsatisfiable : 0
% 0.42/0.60  #    Propositional clauses             : 0
% 0.42/0.60  #    Propositional clauses after purity: 0
% 0.42/0.60  #    Propositional unsat core size     : 0
% 0.42/0.60  #    Propositional preprocessing time  : 0.000
% 0.42/0.60  #    Propositional encoding time       : 0.000
% 0.42/0.60  #    Propositional solver time         : 0.000
% 0.42/0.60  #    Success case prop preproc time    : 0.000
% 0.42/0.60  #    Success case prop encoding time   : 0.000
% 0.42/0.60  #    Success case prop solver time     : 0.000
% 0.42/0.60  # Current number of processed clauses  : 666
% 0.42/0.60  #    Positive orientable unit clauses  : 43
% 0.42/0.60  #    Positive unorientable unit clauses: 0
% 0.42/0.60  #    Negative unit clauses             : 1
% 0.42/0.60  #    Non-unit-clauses                  : 622
% 0.42/0.60  # Current number of unprocessed clauses: 6412
% 0.42/0.60  # ...number of literals in the above   : 28726
% 0.42/0.60  # Current number of archived formulas  : 0
% 0.42/0.60  # Current number of archived clauses   : 467
% 0.42/0.60  # Clause-clause subsumption calls (NU) : 206691
% 0.42/0.60  # Rec. Clause-clause subsumption calls : 101658
% 0.42/0.60  # Non-unit clause-clause subsumptions  : 1564
% 0.42/0.60  # Unit Clause-clause subsumption calls : 3116
% 0.42/0.60  # Rewrite failures with RHS unbound    : 0
% 0.42/0.60  # BW rewrite match attempts            : 68
% 0.42/0.60  # BW rewrite match successes           : 34
% 0.42/0.60  # Condensation attempts                : 0
% 0.42/0.60  # Condensation successes               : 0
% 0.42/0.60  # Termbank termtop insertions          : 202639
% 0.42/0.60  
% 0.42/0.60  # -------------------------------------------------
% 0.42/0.60  # User time                : 0.247 s
% 0.42/0.60  # System time              : 0.012 s
% 0.42/0.60  # Total time               : 0.258 s
% 0.42/0.60  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
