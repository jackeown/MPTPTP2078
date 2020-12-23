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
% DateTime   : Thu Dec  3 10:46:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 871 expanded)
%              Number of clauses        :   77 ( 416 expanded)
%              Number of leaves         :   21 ( 216 expanded)
%              Depth                    :   18
%              Number of atoms          :  260 (2226 expanded)
%              Number of equality atoms :   43 ( 381 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_subset_1])).

fof(c_0_22,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X42,X41)
        | r2_hidden(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ r2_hidden(X42,X41)
        | m1_subset_1(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ m1_subset_1(X42,X41)
        | v1_xboole_0(X42)
        | ~ v1_xboole_0(X41) )
      & ( ~ v1_xboole_0(X42)
        | m1_subset_1(X42,X41)
        | ~ v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & ( ~ r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))
      | ~ r1_tarski(esk4_0,esk5_0) )
    & ( r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))
      | r1_tarski(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_24,plain,(
    ! [X47] : ~ v1_xboole_0(k1_zfmisc_1(X47)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_25,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X34,X33)
        | r1_tarski(X34,X32)
        | X33 != k1_zfmisc_1(X32) )
      & ( ~ r1_tarski(X35,X32)
        | r2_hidden(X35,X33)
        | X33 != k1_zfmisc_1(X32) )
      & ( ~ r2_hidden(esk2_2(X36,X37),X37)
        | ~ r1_tarski(esk2_2(X36,X37),X36)
        | X37 = k1_zfmisc_1(X36) )
      & ( r2_hidden(esk2_2(X36,X37),X37)
        | r1_tarski(esk2_2(X36,X37),X36)
        | X37 = k1_zfmisc_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_26,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_35,plain,(
    ! [X39,X40] :
      ( ~ r1_tarski(X39,X40)
      | r1_tarski(k1_zfmisc_1(X39),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_36,plain,(
    ! [X30,X31] : r1_tarski(X30,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_37,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_40,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_xboole_0(X25,X26)
      | k3_xboole_0(X25,k2_xboole_0(X26,X27)) = k3_xboole_0(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_46,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_38]),c_0_29])).

fof(c_0_48,plain,(
    ! [X45,X46] : m1_subset_1(k6_subset_1(X45,X46),k1_zfmisc_1(X45)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_49,plain,(
    ! [X50,X51] : k6_subset_1(X50,X51) = k4_xboole_0(X50,X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_54,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_47])).

cnf(c_0_58,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_60,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk5_0,k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_67,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_56])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk3_0) = esk5_0
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_71,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | k3_subset_1(X43,X44) = k4_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_42])).

fof(c_0_73,plain,(
    ! [X52,X53,X54] :
      ( ( ~ r1_xboole_0(X53,X54)
        | r1_tarski(X53,k3_subset_1(X52,X54))
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | ~ m1_subset_1(X53,k1_zfmisc_1(X52)) )
      & ( ~ r1_tarski(X53,k3_subset_1(X52,X54))
        | r1_xboole_0(X53,X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | ~ m1_subset_1(X53,k1_zfmisc_1(X52)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_74,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk3_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_53])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_56])).

cnf(c_0_84,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk4_0
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_79])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_82]),c_0_29])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_68])).

fof(c_0_88,plain,(
    ! [X22,X23,X24] :
      ( ( r1_xboole_0(X22,k2_xboole_0(X23,X24))
        | ~ r1_xboole_0(X22,X23)
        | ~ r1_xboole_0(X22,X24) )
      & ( r1_xboole_0(X22,X23)
        | ~ r1_xboole_0(X22,k2_xboole_0(X23,X24)) )
      & ( r1_xboole_0(X22,X24)
        | ~ r1_xboole_0(X22,k2_xboole_0(X23,X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_89,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_90,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_68])).

cnf(c_0_91,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_70])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))
    | r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk5_0) = k3_subset_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_77]),c_0_28])])).

cnf(c_0_96,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_97,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk3_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_77])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(X1,k3_subset_1(esk3_0,esk5_0)))
    | r1_tarski(esk4_0,esk5_0)
    | ~ r1_tarski(k3_subset_1(esk3_0,esk5_0),X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,esk5_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_47])).

fof(c_0_103,plain,(
    ! [X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | k3_subset_1(X48,k3_subset_1(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_104,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_38])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_95])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk3_0,k3_subset_1(esk3_0,esk5_0)))
    | r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])])).

cnf(c_0_109,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | ~ r1_tarski(X1,k5_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk4_0) = k3_subset_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_91]),c_0_38])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_81])).

cnf(c_0_113,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk5_0),X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_28])])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_116,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | ~ r1_tarski(X1,k3_subset_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_101]),c_0_114])])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_114])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.029 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t44_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 0.20/0.42  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.42  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.42  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.42  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.20/0.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.42  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.42  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.20/0.42  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.42  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.20/0.42  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.42  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.42  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.42  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 0.20/0.42  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.42  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.42  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.42  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t44_subset_1])).
% 0.20/0.42  fof(c_0_22, plain, ![X41, X42]:(((~m1_subset_1(X42,X41)|r2_hidden(X42,X41)|v1_xboole_0(X41))&(~r2_hidden(X42,X41)|m1_subset_1(X42,X41)|v1_xboole_0(X41)))&((~m1_subset_1(X42,X41)|v1_xboole_0(X42)|~v1_xboole_0(X41))&(~v1_xboole_0(X42)|m1_subset_1(X42,X41)|~v1_xboole_0(X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.42  fof(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&((~r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))|~r1_tarski(esk4_0,esk5_0))&(r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))|r1_tarski(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.42  fof(c_0_24, plain, ![X47]:~v1_xboole_0(k1_zfmisc_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.42  fof(c_0_25, plain, ![X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X34,X33)|r1_tarski(X34,X32)|X33!=k1_zfmisc_1(X32))&(~r1_tarski(X35,X32)|r2_hidden(X35,X33)|X33!=k1_zfmisc_1(X32)))&((~r2_hidden(esk2_2(X36,X37),X37)|~r1_tarski(esk2_2(X36,X37),X36)|X37=k1_zfmisc_1(X36))&(r2_hidden(esk2_2(X36,X37),X37)|r1_tarski(esk2_2(X36,X37),X36)|X37=k1_zfmisc_1(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.42  fof(c_0_26, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.42  cnf(c_0_27, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_29, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.20/0.42  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.42  fof(c_0_35, plain, ![X39, X40]:(~r1_tarski(X39,X40)|r1_tarski(k1_zfmisc_1(X39),k1_zfmisc_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.20/0.42  fof(c_0_36, plain, ![X30, X31]:r1_tarski(X30,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.42  fof(c_0_37, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  fof(c_0_39, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.42  fof(c_0_40, plain, ![X25, X26, X27]:(~r1_xboole_0(X25,X26)|k3_xboole_0(X25,k2_xboole_0(X26,X27))=k3_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.42  cnf(c_0_42, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.42  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.42  fof(c_0_45, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.42  fof(c_0_46, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_38]), c_0_29])).
% 0.20/0.42  fof(c_0_48, plain, ![X45, X46]:m1_subset_1(k6_subset_1(X45,X46),k1_zfmisc_1(X45)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.20/0.42  fof(c_0_49, plain, ![X50, X51]:k6_subset_1(X50,X51)=k4_xboole_0(X50,X51), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.42  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.42  cnf(c_0_51, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.42  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.42  fof(c_0_54, plain, ![X14, X15]:(~r1_xboole_0(X14,X15)|r1_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.42  cnf(c_0_55, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (r2_hidden(esk4_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_47])).
% 0.20/0.42  cnf(c_0_58, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_59, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  fof(c_0_60, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.42  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (r1_tarski(esk5_0,k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.42  cnf(c_0_63, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_64, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_57])).
% 0.20/0.42  cnf(c_0_66, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_67, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_56])).
% 0.20/0.42  cnf(c_0_68, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (k3_xboole_0(esk5_0,esk3_0)=esk5_0|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.42  cnf(c_0_70, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.42  fof(c_0_71, plain, ![X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|k3_subset_1(X43,X44)=k4_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_42])).
% 0.20/0.42  fof(c_0_73, plain, ![X52, X53, X54]:((~r1_xboole_0(X53,X54)|r1_tarski(X53,k3_subset_1(X52,X54))|~m1_subset_1(X54,k1_zfmisc_1(X52))|~m1_subset_1(X53,k1_zfmisc_1(X52)))&(~r1_tarski(X53,k3_subset_1(X52,X54))|r1_xboole_0(X53,X54)|~m1_subset_1(X54,k1_zfmisc_1(X52))|~m1_subset_1(X53,k1_zfmisc_1(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 0.20/0.42  cnf(c_0_74, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_75, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_66])).
% 0.20/0.42  cnf(c_0_76, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (k3_xboole_0(esk5_0,esk3_0)=esk5_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.42  cnf(c_0_78, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_53])).
% 0.20/0.42  cnf(c_0_80, plain, (r1_tarski(X1,k3_subset_1(X3,X2))|~r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.42  cnf(c_0_81, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_29])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (m1_subset_1(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.42  cnf(c_0_83, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_78, c_0_56])).
% 0.20/0.42  cnf(c_0_84, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk4_0|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_79])).
% 0.20/0.42  cnf(c_0_85, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_xboole_0(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (r2_hidden(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_82]), c_0_29])).
% 0.20/0.42  cnf(c_0_87, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_83, c_0_68])).
% 0.20/0.42  fof(c_0_88, plain, ![X22, X23, X24]:((r1_xboole_0(X22,k2_xboole_0(X23,X24))|~r1_xboole_0(X22,X23)|~r1_xboole_0(X22,X24))&((r1_xboole_0(X22,X23)|~r1_xboole_0(X22,k2_xboole_0(X23,X24)))&(r1_xboole_0(X22,X24)|~r1_xboole_0(X22,k2_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.42  fof(c_0_89, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.42  cnf(c_0_90, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_64, c_0_68])).
% 0.20/0.42  cnf(c_0_91, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_84, c_0_70])).
% 0.20/0.42  cnf(c_0_92, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~r1_xboole_0(X1,X3)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_85, c_0_81])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))|r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_86])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (k5_xboole_0(esk3_0,esk5_0)=k3_subset_1(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_77]), c_0_28])])).
% 0.20/0.42  cnf(c_0_96, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.42  cnf(c_0_97, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.42  cnf(c_0_99, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk3_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_77])).
% 0.20/0.42  cnf(c_0_100, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(X1,k3_subset_1(esk3_0,esk5_0)))|r1_tarski(esk4_0,esk5_0)|~r1_tarski(k3_subset_1(esk3_0,esk5_0),X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,esk5_0),esk3_0)), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_47])).
% 0.20/0.42  fof(c_0_103, plain, ![X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|k3_subset_1(X48,k3_subset_1(X48,X49))=X49), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.42  cnf(c_0_104, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.20/0.42  cnf(c_0_105, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_98])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_38])).
% 0.20/0.42  cnf(c_0_107, negated_conjecture, (r1_xboole_0(k3_subset_1(esk3_0,esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_99, c_0_95])).
% 0.20/0.42  cnf(c_0_108, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk3_0,k3_subset_1(esk3_0,esk5_0)))|r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])])).
% 0.20/0.42  cnf(c_0_109, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.20/0.42  cnf(c_0_110, negated_conjecture, (r1_xboole_0(esk4_0,X1)|~r1_tarski(X1,k5_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.20/0.42  cnf(c_0_111, negated_conjecture, (k5_xboole_0(esk3_0,esk4_0)=k3_subset_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_91]), c_0_38])])).
% 0.20/0.42  cnf(c_0_112, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk3_0,esk4_0))|~r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_81])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (r1_xboole_0(k3_subset_1(esk3_0,esk5_0),X1)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_104, c_0_107])).
% 0.20/0.42  cnf(c_0_114, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_28])])).
% 0.20/0.42  cnf(c_0_115, negated_conjecture, (~r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))|~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_116, negated_conjecture, (r1_xboole_0(esk4_0,X1)|~r1_tarski(X1,k3_subset_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_110, c_0_111])).
% 0.20/0.42  cnf(c_0_117, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_101]), c_0_114])])).
% 0.20/0.42  cnf(c_0_118, negated_conjecture, (~r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_114])])).
% 0.20/0.42  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_118]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 120
% 0.20/0.42  # Proof object clause steps            : 77
% 0.20/0.42  # Proof object formula steps           : 43
% 0.20/0.42  # Proof object conjectures             : 43
% 0.20/0.42  # Proof object clause conjectures      : 40
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 26
% 0.20/0.42  # Proof object initial formulas used   : 21
% 0.20/0.42  # Proof object generating inferences   : 42
% 0.20/0.42  # Proof object simplifying inferences  : 27
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 21
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 35
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 33
% 0.20/0.42  # Processed clauses                    : 716
% 0.20/0.42  # ...of these trivial                  : 41
% 0.20/0.42  # ...subsumed                          : 288
% 0.20/0.42  # ...remaining for further processing  : 387
% 0.20/0.42  # Other redundant clauses eliminated   : 2
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 4
% 0.20/0.42  # Backward-rewritten                   : 67
% 0.20/0.42  # Generated clauses                    : 1639
% 0.20/0.42  # ...of the previous two non-trivial   : 1494
% 0.20/0.42  # Contextual simplify-reflections      : 2
% 0.20/0.42  # Paramodulations                      : 1637
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 2
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 281
% 0.20/0.42  #    Positive orientable unit clauses  : 59
% 0.20/0.42  #    Positive unorientable unit clauses: 2
% 0.20/0.42  #    Negative unit clauses             : 2
% 0.20/0.42  #    Non-unit-clauses                  : 218
% 0.20/0.42  # Current number of unprocessed clauses: 809
% 0.20/0.42  # ...number of literals in the above   : 2203
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 106
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 15842
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 12102
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 278
% 0.20/0.42  # Unit Clause-clause subsumption calls : 970
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 57
% 0.20/0.42  # BW rewrite match successes           : 29
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 21213
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.077 s
% 0.20/0.42  # System time              : 0.003 s
% 0.20/0.42  # Total time               : 0.080 s
% 0.20/0.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
