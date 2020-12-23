%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:39 EST 2020

% Result     : Theorem 12.84s
% Output     : CNFRefutation 12.84s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 685 expanded)
%              Number of clauses        :   71 ( 319 expanded)
%              Number of leaves         :   16 ( 168 expanded)
%              Depth                    :   17
%              Number of atoms          :  207 (1848 expanded)
%              Number of equality atoms :   53 ( 251 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_17,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | r1_tarski(X32,X30)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r1_tarski(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r2_hidden(esk1_2(X34,X35),X35)
        | ~ r1_tarski(esk1_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) )
      & ( r2_hidden(esk1_2(X34,X35),X35)
        | r1_tarski(esk1_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_18,plain,(
    ! [X37,X38] :
      ( ( ~ m1_subset_1(X38,X37)
        | r2_hidden(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ r2_hidden(X38,X37)
        | m1_subset_1(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ m1_subset_1(X38,X37)
        | v1_xboole_0(X38)
        | ~ v1_xboole_0(X37) )
      & ( ~ v1_xboole_0(X38)
        | m1_subset_1(X38,X37)
        | ~ v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X41] : ~ v1_xboole_0(k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_28,plain,(
    ! [X19,X20] : r1_tarski(k4_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_29,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | r1_tarski(k4_xboole_0(X18,X17),k4_xboole_0(X18,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_24])).

fof(c_0_38,plain,(
    ! [X10,X11,X12] :
      ( ( r1_tarski(X10,X11)
        | ~ r1_tarski(X10,k4_xboole_0(X11,X12)) )
      & ( r1_xboole_0(X10,X12)
        | ~ r1_tarski(X10,k4_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_40,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k3_subset_1(X39,X40) = k4_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_41,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,k4_xboole_0(X22,X21))
      | X21 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X25,X26,X27] : k4_xboole_0(k4_xboole_0(X25,X26),X27) = k4_xboole_0(X25,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,k4_xboole_0(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_44])).

fof(c_0_53,plain,(
    ! [X28,X29] :
      ( ( ~ r1_xboole_0(X28,X29)
        | k4_xboole_0(X28,X29) = X28 )
      & ( k4_xboole_0(X28,X29) != X28
        | r1_xboole_0(X28,X29) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_56,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_32])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_33])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( X1 = k4_xboole_0(esk4_0,esk2_0)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,k4_xboole_0(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_61])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_48]),c_0_23])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_23])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k4_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k4_xboole_0(esk4_0,esk2_0),X1) = k4_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_60]),c_0_60])).

fof(c_0_77,plain,(
    ! [X23,X24] : k2_xboole_0(X23,k4_xboole_0(X24,X23)) = k2_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) = esk3_0
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_48]),c_0_32])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_48]),c_0_32])]),c_0_42])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_59])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),X1) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_75]),c_0_75])).

fof(c_0_84,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_33])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk4_0)) = esk3_0
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_48]),c_0_23])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_89,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(esk4_0,esk2_0)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_60])).

cnf(c_0_90,plain,
    ( r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_85])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk4_0)) = esk3_0 ),
    inference(sr,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(esk3_0,esk2_0)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_89,c_0_75])).

cnf(c_0_96,plain,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k4_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_60])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk2_0,esk4_0)) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_75])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n022.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:26:55 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 12.84/13.01  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 12.84/13.01  # and selection function SelectComplexExceptUniqMaxHorn.
% 12.84/13.01  #
% 12.84/13.01  # Preprocessing time       : 0.028 s
% 12.84/13.01  # Presaturation interreduction done
% 12.84/13.01  
% 12.84/13.01  # Proof found!
% 12.84/13.01  # SZS status Theorem
% 12.84/13.01  # SZS output start CNFRefutation
% 12.84/13.01  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 12.84/13.01  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.84/13.01  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.84/13.01  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.84/13.01  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 12.84/13.01  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.84/13.01  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.84/13.01  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 12.84/13.01  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 12.84/13.01  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.84/13.01  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 12.84/13.01  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.84/13.01  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.84/13.01  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.84/13.01  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.84/13.01  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.84/13.01  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 12.84/13.01  fof(c_0_17, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|r1_tarski(X32,X30)|X31!=k1_zfmisc_1(X30))&(~r1_tarski(X33,X30)|r2_hidden(X33,X31)|X31!=k1_zfmisc_1(X30)))&((~r2_hidden(esk1_2(X34,X35),X35)|~r1_tarski(esk1_2(X34,X35),X34)|X35=k1_zfmisc_1(X34))&(r2_hidden(esk1_2(X34,X35),X35)|r1_tarski(esk1_2(X34,X35),X34)|X35=k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 12.84/13.01  fof(c_0_18, plain, ![X37, X38]:(((~m1_subset_1(X38,X37)|r2_hidden(X38,X37)|v1_xboole_0(X37))&(~r2_hidden(X38,X37)|m1_subset_1(X38,X37)|v1_xboole_0(X37)))&((~m1_subset_1(X38,X37)|v1_xboole_0(X38)|~v1_xboole_0(X37))&(~v1_xboole_0(X38)|m1_subset_1(X38,X37)|~v1_xboole_0(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 12.84/13.01  fof(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 12.84/13.01  fof(c_0_20, plain, ![X41]:~v1_xboole_0(k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 12.84/13.01  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.84/13.01  cnf(c_0_22, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.84/13.01  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.84/13.01  cnf(c_0_24, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 12.84/13.01  fof(c_0_25, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 12.84/13.01  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_21])).
% 12.84/13.01  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 12.84/13.01  fof(c_0_28, plain, ![X19, X20]:r1_tarski(k4_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 12.84/13.01  fof(c_0_29, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 12.84/13.01  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 12.84/13.01  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 12.84/13.01  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.84/13.01  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 12.84/13.01  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 12.84/13.01  fof(c_0_35, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|r1_tarski(k4_xboole_0(X18,X17),k4_xboole_0(X18,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 12.84/13.01  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 12.84/13.01  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_32]), c_0_24])).
% 12.84/13.01  fof(c_0_38, plain, ![X10, X11, X12]:((r1_tarski(X10,X11)|~r1_tarski(X10,k4_xboole_0(X11,X12)))&(r1_xboole_0(X10,X12)|~r1_tarski(X10,k4_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 12.84/13.01  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 12.84/13.01  fof(c_0_40, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k3_subset_1(X39,X40)=k4_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 12.84/13.01  fof(c_0_41, plain, ![X21, X22]:(~r1_tarski(X21,k4_xboole_0(X22,X21))|X21=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 12.84/13.01  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 12.84/13.01  cnf(c_0_43, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_33])).
% 12.84/13.01  cnf(c_0_44, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 12.84/13.01  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 12.84/13.01  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_39, c_0_33])).
% 12.84/13.01  cnf(c_0_47, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.84/13.01  cnf(c_0_48, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 12.84/13.01  fof(c_0_49, plain, ![X25, X26, X27]:k4_xboole_0(k4_xboole_0(X25,X26),X27)=k4_xboole_0(X25,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 12.84/13.01  cnf(c_0_50, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 12.84/13.01  cnf(c_0_51, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,k4_xboole_0(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 12.84/13.01  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_44])).
% 12.84/13.01  fof(c_0_53, plain, ![X28, X29]:((~r1_xboole_0(X28,X29)|k4_xboole_0(X28,X29)=X28)&(k4_xboole_0(X28,X29)!=X28|r1_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 12.84/13.01  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 12.84/13.01  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 12.84/13.01  fof(c_0_56, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 12.84/13.01  cnf(c_0_57, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0))|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_32])])).
% 12.84/13.01  cnf(c_0_58, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 12.84/13.01  cnf(c_0_59, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 12.84/13.01  cnf(c_0_60, negated_conjecture, (k1_xboole_0=k4_xboole_0(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 12.84/13.01  cnf(c_0_61, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_33])).
% 12.84/13.01  cnf(c_0_62, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 12.84/13.01  cnf(c_0_63, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 12.84/13.01  cnf(c_0_64, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 12.84/13.01  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_57])).
% 12.84/13.01  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.84/13.01  cnf(c_0_67, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 12.84/13.01  cnf(c_0_68, plain, (X1=k4_xboole_0(esk4_0,esk2_0)|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_50, c_0_60])).
% 12.84/13.01  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_61])).
% 12.84/13.01  cnf(c_0_70, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 12.84/13.01  cnf(c_0_71, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 12.84/13.01  cnf(c_0_72, negated_conjecture, (~r1_tarski(k4_xboole_0(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))|~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_48]), c_0_23])])).
% 12.84/13.01  cnf(c_0_73, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_23])])).
% 12.84/13.01  cnf(c_0_74, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k4_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_67, c_0_60])).
% 12.84/13.01  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 12.84/13.01  cnf(c_0_76, plain, (k4_xboole_0(k4_xboole_0(esk4_0,esk2_0),X1)=k4_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_60]), c_0_60])).
% 12.84/13.01  fof(c_0_77, plain, ![X23, X24]:k2_xboole_0(X23,k4_xboole_0(X24,X23))=k2_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 12.84/13.01  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))=esk3_0|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_71])).
% 12.84/13.01  cnf(c_0_79, negated_conjecture, (~r1_tarski(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_48]), c_0_32])])).
% 12.84/13.01  cnf(c_0_80, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_48]), c_0_32])]), c_0_42])).
% 12.84/13.01  cnf(c_0_81, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_59])).
% 12.84/13.01  cnf(c_0_82, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 12.84/13.01  cnf(c_0_83, plain, (k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),X1)=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_75]), c_0_75])).
% 12.84/13.01  fof(c_0_84, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 12.84/13.01  cnf(c_0_85, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 12.84/13.01  cnf(c_0_86, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_54, c_0_33])).
% 12.84/13.01  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk4_0))=esk3_0|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_48]), c_0_23])])).
% 12.84/13.01  cnf(c_0_88, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 12.84/13.01  cnf(c_0_89, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(esk4_0,esk2_0)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_81, c_0_60])).
% 12.84/13.01  cnf(c_0_90, plain, (r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 12.84/13.01  cnf(c_0_91, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 12.84/13.01  cnf(c_0_92, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_59, c_0_85])).
% 12.84/13.01  cnf(c_0_93, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_62, c_0_86])).
% 12.84/13.01  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk4_0))=esk3_0), inference(sr,[status(thm)],[c_0_87, c_0_88])).
% 12.84/13.01  cnf(c_0_95, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(esk3_0,esk2_0)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_89, c_0_75])).
% 12.84/13.01  cnf(c_0_96, plain, (r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 12.84/13.01  cnf(c_0_97, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k4_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_58, c_0_60])).
% 12.84/13.01  cnf(c_0_98, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_59, c_0_92])).
% 12.84/13.01  cnf(c_0_99, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk2_0,esk4_0))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 12.84/13.01  cnf(c_0_100, plain, (k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 12.84/13.01  cnf(c_0_101, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_97, c_0_75])).
% 12.84/13.01  cnf(c_0_102, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])).
% 12.84/13.01  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_88]), ['proof']).
% 12.84/13.01  # SZS output end CNFRefutation
% 12.84/13.01  # Proof object total steps             : 104
% 12.84/13.01  # Proof object clause steps            : 71
% 12.84/13.01  # Proof object formula steps           : 33
% 12.84/13.01  # Proof object conjectures             : 33
% 12.84/13.01  # Proof object clause conjectures      : 30
% 12.84/13.01  # Proof object formula conjectures     : 3
% 12.84/13.01  # Proof object initial clauses used    : 21
% 12.84/13.01  # Proof object initial formulas used   : 16
% 12.84/13.01  # Proof object generating inferences   : 38
% 12.84/13.01  # Proof object simplifying inferences  : 32
% 12.84/13.01  # Training examples: 0 positive, 0 negative
% 12.84/13.01  # Parsed axioms                        : 16
% 12.84/13.01  # Removed by relevancy pruning/SinE    : 0
% 12.84/13.01  # Initial clauses                      : 28
% 12.84/13.01  # Removed in clause preprocessing      : 0
% 12.84/13.01  # Initial clauses in saturation        : 28
% 12.84/13.01  # Processed clauses                    : 51168
% 12.84/13.01  # ...of these trivial                  : 665
% 12.84/13.01  # ...subsumed                          : 47053
% 12.84/13.01  # ...remaining for further processing  : 3450
% 12.84/13.01  # Other redundant clauses eliminated   : 1835
% 12.84/13.01  # Clauses deleted for lack of memory   : 0
% 12.84/13.01  # Backward-subsumed                    : 247
% 12.84/13.01  # Backward-rewritten                   : 428
% 12.84/13.01  # Generated clauses                    : 1856210
% 12.84/13.01  # ...of the previous two non-trivial   : 1711865
% 12.84/13.01  # Contextual simplify-reflections      : 42
% 12.84/13.01  # Paramodulations                      : 1854210
% 12.84/13.01  # Factorizations                       : 80
% 12.84/13.01  # Equation resolutions                 : 1908
% 12.84/13.01  # Propositional unsat checks           : 0
% 12.84/13.01  #    Propositional check models        : 0
% 12.84/13.01  #    Propositional check unsatisfiable : 0
% 12.84/13.01  #    Propositional clauses             : 0
% 12.84/13.01  #    Propositional clauses after purity: 0
% 12.84/13.01  #    Propositional unsat core size     : 0
% 12.84/13.01  #    Propositional preprocessing time  : 0.000
% 12.84/13.01  #    Propositional encoding time       : 0.000
% 12.84/13.01  #    Propositional solver time         : 0.000
% 12.84/13.01  #    Success case prop preproc time    : 0.000
% 12.84/13.01  #    Success case prop encoding time   : 0.000
% 12.84/13.01  #    Success case prop solver time     : 0.000
% 12.84/13.01  # Current number of processed clauses  : 2733
% 12.84/13.01  #    Positive orientable unit clauses  : 554
% 12.84/13.01  #    Positive unorientable unit clauses: 84
% 12.84/13.01  #    Negative unit clauses             : 209
% 12.84/13.01  #    Non-unit-clauses                  : 1886
% 12.84/13.01  # Current number of unprocessed clauses: 1655071
% 12.84/13.01  # ...number of literals in the above   : 4604864
% 12.84/13.01  # Current number of archived formulas  : 0
% 12.84/13.01  # Current number of archived clauses   : 715
% 12.84/13.01  # Clause-clause subsumption calls (NU) : 2725232
% 12.84/13.01  # Rec. Clause-clause subsumption calls : 1198852
% 12.84/13.01  # Non-unit clause-clause subsumptions  : 15040
% 12.84/13.01  # Unit Clause-clause subsumption calls : 142334
% 12.84/13.01  # Rewrite failures with RHS unbound    : 39
% 12.84/13.01  # BW rewrite match attempts            : 11418
% 12.84/13.01  # BW rewrite match successes           : 3668
% 12.84/13.01  # Condensation attempts                : 0
% 12.84/13.01  # Condensation successes               : 0
% 12.84/13.01  # Termbank termtop insertions          : 25539381
% 12.84/13.06  
% 12.84/13.06  # -------------------------------------------------
% 12.84/13.06  # User time                : 12.136 s
% 12.84/13.06  # System time              : 0.582 s
% 12.84/13.06  # Total time               : 12.718 s
% 12.84/13.06  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
