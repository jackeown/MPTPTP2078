%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:20 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 273 expanded)
%              Number of clauses        :   70 ( 128 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  185 ( 634 expanded)
%              Number of equality atoms :   55 ( 147 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_18,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | r1_tarski(X28,X26)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r1_tarski(X29,X26)
        | r2_hidden(X29,X27)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r2_hidden(esk1_2(X30,X31),X31)
        | ~ r1_tarski(esk1_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) )
      & ( r2_hidden(esk1_2(X30,X31),X31)
        | r1_tarski(esk1_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_20,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_21,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_22,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | k3_subset_1(X40,k3_subset_1(X40,X41)) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_23,plain,(
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

fof(c_0_24,plain,(
    ! [X39] : ~ v1_xboole_0(k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_27,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_28,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_45,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( k3_subset_1(X1,X2) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_36])).

fof(c_0_48,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k2_xboole_0(X22,X23)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_53,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( k3_subset_1(X1,k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k3_subset_1(esk2_0,esk4_0) = k4_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_51])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_56])).

cnf(c_0_64,plain,
    ( k3_subset_1(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_57])).

fof(c_0_65,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k3_subset_1(esk2_0,k4_xboole_0(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_61])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_71,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_66]),c_0_67])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_70])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_72])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_79,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(k4_xboole_0(X19,X20),X21)
      | r1_tarski(X19,k2_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_83,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k4_subset_1(X42,X43,X44) = k2_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,esk4_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_88,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_87]),c_0_36])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_93,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k4_subset_1(esk2_0,X1,esk4_0) = k2_xboole_0(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_51])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_31])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_31])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk4_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_87])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_99])).

cnf(c_0_102,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_86])).

cnf(c_0_104,negated_conjecture,
    ( k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_101])).

cnf(c_0_105,plain,
    ( r2_hidden(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_70])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.20/0.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.027 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.51  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.51  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.51  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.51  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.51  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.51  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.51  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.51  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.51  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.51  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.51  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 0.20/0.51  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.51  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.51  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.51  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.51  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.20/0.51  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.20/0.51  fof(c_0_18, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|r1_tarski(X28,X26)|X27!=k1_zfmisc_1(X26))&(~r1_tarski(X29,X26)|r2_hidden(X29,X27)|X27!=k1_zfmisc_1(X26)))&((~r2_hidden(esk1_2(X30,X31),X31)|~r1_tarski(esk1_2(X30,X31),X30)|X31=k1_zfmisc_1(X30))&(r2_hidden(esk1_2(X30,X31),X31)|r1_tarski(esk1_2(X30,X31),X30)|X31=k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.51  fof(c_0_19, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.51  fof(c_0_20, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.51  fof(c_0_21, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.51  fof(c_0_22, plain, ![X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|k3_subset_1(X40,k3_subset_1(X40,X41))=X41), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.51  fof(c_0_23, plain, ![X33, X34]:(((~m1_subset_1(X34,X33)|r2_hidden(X34,X33)|v1_xboole_0(X33))&(~r2_hidden(X34,X33)|m1_subset_1(X34,X33)|v1_xboole_0(X33)))&((~m1_subset_1(X34,X33)|v1_xboole_0(X34)|~v1_xboole_0(X33))&(~v1_xboole_0(X34)|m1_subset_1(X34,X33)|~v1_xboole_0(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.51  fof(c_0_24, plain, ![X39]:~v1_xboole_0(k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.51  cnf(c_0_25, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  fof(c_0_26, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.51  fof(c_0_27, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.51  fof(c_0_28, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.51  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  fof(c_0_32, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.51  fof(c_0_33, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 0.20/0.51  cnf(c_0_34, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.51  cnf(c_0_36, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_37, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.51  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.51  cnf(c_0_39, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.51  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.51  cnf(c_0_41, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.51  cnf(c_0_42, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.51  cnf(c_0_43, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.51  fof(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.20/0.51  cnf(c_0_45, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.20/0.51  cnf(c_0_46, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.51  cnf(c_0_47, plain, (k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_36])).
% 0.20/0.51  fof(c_0_48, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.51  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.51  cnf(c_0_50, plain, (r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_36])).
% 0.20/0.51  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  fof(c_0_52, plain, ![X22, X23]:k4_xboole_0(X22,k2_xboole_0(X22,X23))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.51  cnf(c_0_53, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.51  cnf(c_0_54, plain, (k3_subset_1(X1,k1_xboole_0)=k4_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.20/0.51  cnf(c_0_55, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.51  cnf(c_0_56, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.20/0.51  cnf(c_0_57, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_49])).
% 0.20/0.51  cnf(c_0_58, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.51  cnf(c_0_59, negated_conjecture, (k3_subset_1(esk2_0,esk4_0)=k4_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 0.20/0.51  cnf(c_0_60, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_34, c_0_51])).
% 0.20/0.51  cnf(c_0_61, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.51  cnf(c_0_62, plain, (k3_subset_1(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.51  cnf(c_0_63, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_56])).
% 0.20/0.51  cnf(c_0_64, plain, (k3_subset_1(X1,X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_47, c_0_57])).
% 0.20/0.51  fof(c_0_65, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.51  cnf(c_0_66, negated_conjecture, (r2_hidden(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.51  cnf(c_0_67, negated_conjecture, (k3_subset_1(esk2_0,k4_xboole_0(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_60, c_0_59])).
% 0.20/0.51  cnf(c_0_68, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_41, c_0_61])).
% 0.20/0.51  cnf(c_0_69, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.20/0.51  cnf(c_0_70, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.51  fof(c_0_71, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.51  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_66]), c_0_67])).
% 0.20/0.51  cnf(c_0_73, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.51  cnf(c_0_74, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_55, c_0_70])).
% 0.20/0.51  cnf(c_0_75, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.51  cnf(c_0_76, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_72])).
% 0.20/0.51  cnf(c_0_77, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.20/0.51  cnf(c_0_78, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.51  fof(c_0_79, plain, ![X19, X20, X21]:(~r1_tarski(k4_xboole_0(X19,X20),X21)|r1_tarski(X19,k2_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.20/0.51  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.51  cnf(c_0_81, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.51  cnf(c_0_82, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  fof(c_0_83, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|~m1_subset_1(X44,k1_zfmisc_1(X42))|k4_subset_1(X42,X43,X44)=k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.20/0.51  cnf(c_0_84, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.51  cnf(c_0_85, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,esk4_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.51  cnf(c_0_86, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_82])).
% 0.20/0.51  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  cnf(c_0_88, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.51  cnf(c_0_89, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.51  cnf(c_0_90, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_86])).
% 0.20/0.51  cnf(c_0_91, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_87]), c_0_36])).
% 0.20/0.51  cnf(c_0_92, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  cnf(c_0_93, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_87])).
% 0.20/0.51  cnf(c_0_94, negated_conjecture, (k4_subset_1(esk2_0,X1,esk4_0)=k2_xboole_0(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_51])).
% 0.20/0.51  cnf(c_0_95, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_89, c_0_31])).
% 0.20/0.51  cnf(c_0_96, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_31])).
% 0.20/0.51  cnf(c_0_97, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.51  cnf(c_0_98, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk4_0)=k2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_94, c_0_87])).
% 0.20/0.51  cnf(c_0_99, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.51  cnf(c_0_100, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.51  cnf(c_0_101, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_99])).
% 0.20/0.51  cnf(c_0_102, plain, (r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 0.20/0.51  cnf(c_0_103, negated_conjecture, (~r2_hidden(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_100, c_0_86])).
% 0.20/0.51  cnf(c_0_104, negated_conjecture, (k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_101])).
% 0.20/0.51  cnf(c_0_105, plain, (r2_hidden(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_102, c_0_70])).
% 0.20/0.51  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104]), c_0_105])]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 107
% 0.20/0.51  # Proof object clause steps            : 70
% 0.20/0.51  # Proof object formula steps           : 37
% 0.20/0.51  # Proof object conjectures             : 29
% 0.20/0.51  # Proof object clause conjectures      : 26
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 22
% 0.20/0.51  # Proof object initial formulas used   : 18
% 0.20/0.51  # Proof object generating inferences   : 39
% 0.20/0.51  # Proof object simplifying inferences  : 20
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 18
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 26
% 0.20/0.51  # Removed in clause preprocessing      : 0
% 0.20/0.51  # Initial clauses in saturation        : 26
% 0.20/0.51  # Processed clauses                    : 1803
% 0.20/0.51  # ...of these trivial                  : 217
% 0.20/0.51  # ...subsumed                          : 1013
% 0.20/0.51  # ...remaining for further processing  : 573
% 0.20/0.51  # Other redundant clauses eliminated   : 2
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 2
% 0.20/0.51  # Backward-rewritten                   : 54
% 0.20/0.51  # Generated clauses                    : 17998
% 0.20/0.51  # ...of the previous two non-trivial   : 10002
% 0.20/0.51  # Contextual simplify-reflections      : 2
% 0.20/0.51  # Paramodulations                      : 17994
% 0.20/0.51  # Factorizations                       : 2
% 0.20/0.51  # Equation resolutions                 : 2
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 489
% 0.20/0.51  #    Positive orientable unit clauses  : 233
% 0.20/0.51  #    Positive unorientable unit clauses: 12
% 0.20/0.51  #    Negative unit clauses             : 1
% 0.20/0.51  #    Non-unit-clauses                  : 243
% 0.20/0.51  # Current number of unprocessed clauses: 8179
% 0.20/0.51  # ...number of literals in the above   : 12955
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 82
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 14261
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 11900
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 763
% 0.20/0.51  # Unit Clause-clause subsumption calls : 2849
% 0.20/0.51  # Rewrite failures with RHS unbound    : 134
% 0.20/0.51  # BW rewrite match attempts            : 874
% 0.20/0.51  # BW rewrite match successes           : 133
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 167046
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.161 s
% 0.20/0.51  # System time              : 0.012 s
% 0.20/0.51  # Total time               : 0.173 s
% 0.20/0.51  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
