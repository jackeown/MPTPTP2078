%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:19 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 174 expanded)
%              Number of clauses        :   50 (  78 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 434 expanded)
%              Number of equality atoms :   44 (  88 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(c_0_16,plain,(
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

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
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

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X39] : ~ v1_xboole_0(k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_23,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | k3_subset_1(X40,k3_subset_1(X40,X41)) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_24,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_31,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

fof(c_0_42,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,k2_xboole_0(X21,X22))
      | r1_tarski(k4_xboole_0(X20,X21),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

fof(c_0_45,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k4_subset_1(X42,X43,X44) = k2_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_46,plain,(
    ! [X8,X9,X10] :
      ( ( r1_tarski(X8,X9)
        | ~ r1_tarski(X8,k4_xboole_0(X9,X10)) )
      & ( r1_xboole_0(X8,X10)
        | ~ r1_tarski(X8,k4_xboole_0(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_47,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k3_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk2_0),esk4_0) = k4_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_51,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_52,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_41]),c_0_48]),c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),X2)
    | ~ r1_tarski(k4_xboole_0(X1,esk2_0),k2_xboole_0(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k4_subset_1(esk2_0,X1,esk4_0) = k2_xboole_0(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_61,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(k4_xboole_0(X23,X24),X25)
      | r1_tarski(X23,k2_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(esk4_0,X1),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( k4_subset_1(esk2_0,X1,esk4_0) = k2_xboole_0(X1,esk4_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33]),c_0_29])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_38])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_41])).

cnf(c_0_73,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk4_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,plain,
    ( k3_subset_1(X1,X2) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_60]),c_0_29])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_26])).

cnf(c_0_80,negated_conjecture,
    ( k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_43])).

cnf(c_0_81,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_57])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:06:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.62/0.79  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.62/0.79  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.62/0.79  #
% 0.62/0.79  # Preprocessing time       : 0.028 s
% 0.62/0.79  # Presaturation interreduction done
% 0.62/0.79  
% 0.62/0.79  # Proof found!
% 0.62/0.79  # SZS status Theorem
% 0.62/0.79  # SZS output start CNFRefutation
% 0.62/0.79  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.62/0.79  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 0.62/0.79  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.62/0.79  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.62/0.79  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.62/0.79  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.62/0.79  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.62/0.79  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.62/0.79  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.62/0.79  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.62/0.79  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.62/0.79  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.62/0.79  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.62/0.79  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.62/0.79  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.62/0.79  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.62/0.79  fof(c_0_16, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|r1_tarski(X28,X26)|X27!=k1_zfmisc_1(X26))&(~r1_tarski(X29,X26)|r2_hidden(X29,X27)|X27!=k1_zfmisc_1(X26)))&((~r2_hidden(esk1_2(X30,X31),X31)|~r1_tarski(esk1_2(X30,X31),X30)|X31=k1_zfmisc_1(X30))&(r2_hidden(esk1_2(X30,X31),X31)|r1_tarski(esk1_2(X30,X31),X30)|X31=k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.62/0.79  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 0.62/0.79  fof(c_0_18, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.62/0.79  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.62/0.79  fof(c_0_20, plain, ![X33, X34]:(((~m1_subset_1(X34,X33)|r2_hidden(X34,X33)|v1_xboole_0(X33))&(~r2_hidden(X34,X33)|m1_subset_1(X34,X33)|v1_xboole_0(X33)))&((~m1_subset_1(X34,X33)|v1_xboole_0(X34)|~v1_xboole_0(X33))&(~v1_xboole_0(X34)|m1_subset_1(X34,X33)|~v1_xboole_0(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.62/0.79  fof(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.62/0.79  fof(c_0_22, plain, ![X39]:~v1_xboole_0(k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.62/0.79  fof(c_0_23, plain, ![X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|k3_subset_1(X40,k3_subset_1(X40,X41))=X41), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.62/0.79  fof(c_0_24, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.62/0.79  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.79  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_19])).
% 0.62/0.79  cnf(c_0_27, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.62/0.79  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.79  cnf(c_0_29, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.79  fof(c_0_30, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.62/0.79  fof(c_0_31, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.62/0.79  cnf(c_0_32, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.62/0.79  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.79  cnf(c_0_34, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.62/0.79  fof(c_0_35, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.62/0.79  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.62/0.79  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.62/0.79  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.79  cnf(c_0_39, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.62/0.79  cnf(c_0_40, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.62/0.79  cnf(c_0_41, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.62/0.79  fof(c_0_42, plain, ![X20, X21, X22]:(~r1_tarski(X20,k2_xboole_0(X21,X22))|r1_tarski(k4_xboole_0(X20,X21),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.62/0.79  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.62/0.79  cnf(c_0_44, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.62/0.79  fof(c_0_45, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|~m1_subset_1(X44,k1_zfmisc_1(X42))|k4_subset_1(X42,X43,X44)=k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.62/0.79  fof(c_0_46, plain, ![X8, X9, X10]:((r1_tarski(X8,X9)|~r1_tarski(X8,k4_xboole_0(X9,X10)))&(r1_xboole_0(X8,X10)|~r1_tarski(X8,k4_xboole_0(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.62/0.79  cnf(c_0_47, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=k4_xboole_0(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 0.62/0.79  cnf(c_0_48, negated_conjecture, (k3_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.62/0.79  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.62/0.79  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk2_0),esk4_0)=k4_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.62/0.79  fof(c_0_51, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.62/0.79  fof(c_0_52, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.62/0.79  cnf(c_0_53, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.62/0.79  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.62/0.79  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_41]), c_0_48]), c_0_41])).
% 0.62/0.79  cnf(c_0_56, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),X2)|~r1_tarski(k4_xboole_0(X1,esk2_0),k2_xboole_0(esk4_0,X2))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.62/0.79  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.62/0.79  cnf(c_0_58, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.62/0.79  cnf(c_0_59, negated_conjecture, (k4_subset_1(esk2_0,X1,esk4_0)=k2_xboole_0(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_28])).
% 0.62/0.79  cnf(c_0_60, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.62/0.79  fof(c_0_61, plain, ![X23, X24, X25]:(~r1_tarski(k4_xboole_0(X23,X24),X25)|r1_tarski(X23,k2_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.62/0.79  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.62/0.79  cnf(c_0_63, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(esk4_0,X1),esk2_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.62/0.79  cnf(c_0_64, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_58])).
% 0.62/0.79  cnf(c_0_65, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.79  cnf(c_0_66, negated_conjecture, (k4_subset_1(esk2_0,X1,esk4_0)=k2_xboole_0(X1,esk4_0)|~r2_hidden(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_29])).
% 0.62/0.79  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_33]), c_0_29])).
% 0.62/0.79  cnf(c_0_68, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.62/0.79  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.62/0.79  cnf(c_0_70, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_38])).
% 0.62/0.79  cnf(c_0_71, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_25, c_0_64])).
% 0.62/0.79  cnf(c_0_72, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_65, c_0_41])).
% 0.62/0.79  cnf(c_0_73, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk4_0)=k2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.62/0.79  cnf(c_0_74, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_68])).
% 0.62/0.79  cnf(c_0_75, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.62/0.79  cnf(c_0_76, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.62/0.79  cnf(c_0_77, plain, (k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_60]), c_0_29])).
% 0.62/0.79  cnf(c_0_78, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.62/0.79  cnf(c_0_79, negated_conjecture, (~r2_hidden(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_76, c_0_26])).
% 0.62/0.79  cnf(c_0_80, negated_conjecture, (k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_43])).
% 0.62/0.79  cnf(c_0_81, plain, (r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_74, c_0_57])).
% 0.62/0.79  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_81])]), ['proof']).
% 0.62/0.79  # SZS output end CNFRefutation
% 0.62/0.79  # Proof object total steps             : 83
% 0.62/0.79  # Proof object clause steps            : 50
% 0.62/0.79  # Proof object formula steps           : 33
% 0.62/0.79  # Proof object conjectures             : 28
% 0.62/0.79  # Proof object clause conjectures      : 25
% 0.62/0.79  # Proof object formula conjectures     : 3
% 0.62/0.79  # Proof object initial clauses used    : 20
% 0.62/0.79  # Proof object initial formulas used   : 16
% 0.62/0.79  # Proof object generating inferences   : 23
% 0.62/0.79  # Proof object simplifying inferences  : 20
% 0.62/0.79  # Training examples: 0 positive, 0 negative
% 0.62/0.79  # Parsed axioms                        : 17
% 0.62/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.79  # Initial clauses                      : 28
% 0.62/0.79  # Removed in clause preprocessing      : 0
% 0.62/0.79  # Initial clauses in saturation        : 28
% 0.62/0.79  # Processed clauses                    : 3403
% 0.62/0.79  # ...of these trivial                  : 446
% 0.62/0.79  # ...subsumed                          : 1883
% 0.62/0.79  # ...remaining for further processing  : 1074
% 0.62/0.79  # Other redundant clauses eliminated   : 4
% 0.62/0.79  # Clauses deleted for lack of memory   : 0
% 0.62/0.79  # Backward-subsumed                    : 97
% 0.62/0.79  # Backward-rewritten                   : 131
% 0.62/0.79  # Generated clauses                    : 51411
% 0.62/0.79  # ...of the previous two non-trivial   : 38340
% 0.62/0.79  # Contextual simplify-reflections      : 2
% 0.62/0.79  # Paramodulations                      : 51405
% 0.62/0.79  # Factorizations                       : 2
% 0.62/0.79  # Equation resolutions                 : 4
% 0.62/0.79  # Propositional unsat checks           : 0
% 0.62/0.79  #    Propositional check models        : 0
% 0.62/0.79  #    Propositional check unsatisfiable : 0
% 0.62/0.79  #    Propositional clauses             : 0
% 0.62/0.79  #    Propositional clauses after purity: 0
% 0.62/0.79  #    Propositional unsat core size     : 0
% 0.62/0.79  #    Propositional preprocessing time  : 0.000
% 0.62/0.79  #    Propositional encoding time       : 0.000
% 0.62/0.79  #    Propositional solver time         : 0.000
% 0.62/0.79  #    Success case prop preproc time    : 0.000
% 0.62/0.79  #    Success case prop encoding time   : 0.000
% 0.62/0.79  #    Success case prop solver time     : 0.000
% 0.62/0.79  # Current number of processed clauses  : 815
% 0.62/0.79  #    Positive orientable unit clauses  : 343
% 0.62/0.79  #    Positive unorientable unit clauses: 26
% 0.62/0.79  #    Negative unit clauses             : 1
% 0.62/0.79  #    Non-unit-clauses                  : 445
% 0.62/0.79  # Current number of unprocessed clauses: 34531
% 0.62/0.79  # ...number of literals in the above   : 52273
% 0.62/0.79  # Current number of archived formulas  : 0
% 0.62/0.79  # Current number of archived clauses   : 255
% 0.62/0.79  # Clause-clause subsumption calls (NU) : 38853
% 0.62/0.79  # Rec. Clause-clause subsumption calls : 31009
% 0.62/0.79  # Non-unit clause-clause subsumptions  : 1895
% 0.62/0.79  # Unit Clause-clause subsumption calls : 2971
% 0.62/0.79  # Rewrite failures with RHS unbound    : 43
% 0.62/0.79  # BW rewrite match attempts            : 1509
% 0.62/0.79  # BW rewrite match successes           : 273
% 0.62/0.79  # Condensation attempts                : 0
% 0.62/0.79  # Condensation successes               : 0
% 0.62/0.79  # Termbank termtop insertions          : 527945
% 0.62/0.79  
% 0.62/0.79  # -------------------------------------------------
% 0.62/0.79  # User time                : 0.419 s
% 0.62/0.79  # System time              : 0.022 s
% 0.62/0.79  # Total time               : 0.441 s
% 0.62/0.79  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
