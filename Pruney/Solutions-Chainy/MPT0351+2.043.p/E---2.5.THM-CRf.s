%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:32 EST 2020

% Result     : Theorem 6.14s
% Output     : CNFRefutation 6.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 350 expanded)
%              Number of clauses        :   37 ( 156 expanded)
%              Number of leaves         :   13 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 758 expanded)
%              Number of equality atoms :   50 ( 325 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t28_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_13,plain,(
    ! [X34,X35] : k3_tarski(k2_tarski(X34,X35)) = k2_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
      | k4_subset_1(X41,X42,X43) = k2_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X27)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r1_tarski(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r2_hidden(esk3_2(X31,X32),X32)
        | ~ r1_tarski(esk3_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) )
      & ( r2_hidden(esk3_2(X31,X32),X32)
        | r1_tarski(esk3_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t28_subset_1])).

fof(c_0_21,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X37,X36)
        | r2_hidden(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ r2_hidden(X37,X36)
        | m1_subset_1(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ m1_subset_1(X37,X36)
        | v1_xboole_0(X37)
        | ~ v1_xboole_0(X36) )
      & ( ~ v1_xboole_0(X37)
        | m1_subset_1(X37,X36)
        | ~ v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_26,plain,(
    ! [X40] : ~ v1_xboole_0(k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_27,plain,(
    ! [X39] : m1_subset_1(k2_subset_1(X39),k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_28,plain,(
    ! [X38] : k2_subset_1(X38) = X38 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_29,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & k4_subset_1(esk4_0,esk5_0,k2_subset_1(esk4_0)) != k2_subset_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_enumset1(X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( X3 = k3_tarski(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_23]),c_0_24])).

cnf(c_0_45,plain,
    ( k4_subset_1(X1,X2,X3) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35])).

cnf(c_0_50,plain,
    ( X3 = k3_tarski(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_23]),c_0_24])).

cnf(c_0_51,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k4_subset_1(esk4_0,esk5_0,k2_subset_1(esk4_0)) != k2_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( k4_subset_1(esk4_0,esk5_0,X1) = k3_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_46]),c_0_35])).

cnf(c_0_55,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_23]),c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k4_subset_1(esk4_0,esk5_0,esk4_0) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_37]),c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( k4_subset_1(esk4_0,esk5_0,esk4_0) = k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,X1)) = X1
    | r2_hidden(esk2_3(esk5_0,X1,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk5_0,esk4_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_60]),c_0_55]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_60]),c_0_55]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 6.14/6.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 6.14/6.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 6.14/6.39  #
% 6.14/6.39  # Preprocessing time       : 0.028 s
% 6.14/6.39  # Presaturation interreduction done
% 6.14/6.39  
% 6.14/6.39  # Proof found!
% 6.14/6.39  # SZS status Theorem
% 6.14/6.39  # SZS output start CNFRefutation
% 6.14/6.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.14/6.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.14/6.39  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.14/6.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.14/6.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.14/6.39  fof(t28_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 6.14/6.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.14/6.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.14/6.39  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.14/6.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.14/6.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.14/6.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.14/6.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.14/6.39  fof(c_0_13, plain, ![X34, X35]:k3_tarski(k2_tarski(X34,X35))=k2_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 6.14/6.39  fof(c_0_14, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.14/6.39  fof(c_0_15, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|~m1_subset_1(X43,k1_zfmisc_1(X41))|k4_subset_1(X41,X42,X43)=k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 6.14/6.39  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.14/6.39  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.14/6.39  fof(c_0_18, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 6.14/6.39  fof(c_0_19, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X29,X28)|r1_tarski(X29,X27)|X28!=k1_zfmisc_1(X27))&(~r1_tarski(X30,X27)|r2_hidden(X30,X28)|X28!=k1_zfmisc_1(X27)))&((~r2_hidden(esk3_2(X31,X32),X32)|~r1_tarski(esk3_2(X31,X32),X31)|X32=k1_zfmisc_1(X31))&(r2_hidden(esk3_2(X31,X32),X32)|r1_tarski(esk3_2(X31,X32),X31)|X32=k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 6.14/6.39  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t28_subset_1])).
% 6.14/6.39  fof(c_0_21, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 6.14/6.39  cnf(c_0_22, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.14/6.39  cnf(c_0_23, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 6.14/6.39  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.14/6.39  fof(c_0_25, plain, ![X36, X37]:(((~m1_subset_1(X37,X36)|r2_hidden(X37,X36)|v1_xboole_0(X36))&(~r2_hidden(X37,X36)|m1_subset_1(X37,X36)|v1_xboole_0(X36)))&((~m1_subset_1(X37,X36)|v1_xboole_0(X37)|~v1_xboole_0(X36))&(~v1_xboole_0(X37)|m1_subset_1(X37,X36)|~v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 6.14/6.39  fof(c_0_26, plain, ![X40]:~v1_xboole_0(k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 6.14/6.39  fof(c_0_27, plain, ![X39]:m1_subset_1(k2_subset_1(X39),k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 6.14/6.39  fof(c_0_28, plain, ![X38]:k2_subset_1(X38)=X38, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 6.14/6.39  fof(c_0_29, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 6.14/6.39  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.14/6.39  fof(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&k4_subset_1(esk4_0,esk5_0,k2_subset_1(esk4_0))!=k2_subset_1(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 6.14/6.39  cnf(c_0_32, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.14/6.39  cnf(c_0_33, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_enumset1(X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 6.14/6.39  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.14/6.39  cnf(c_0_35, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.14/6.39  cnf(c_0_36, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.14/6.39  cnf(c_0_37, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.14/6.39  fof(c_0_38, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 6.14/6.39  cnf(c_0_39, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.14/6.39  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 6.14/6.39  cnf(c_0_41, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.14/6.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 6.14/6.39  cnf(c_0_43, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.14/6.39  cnf(c_0_44, plain, (X3=k3_tarski(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_23]), c_0_24])).
% 6.14/6.39  cnf(c_0_45, plain, (k4_subset_1(X1,X2,X3)=k3_tarski(k2_enumset1(X2,X2,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X3,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 6.14/6.39  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 6.14/6.39  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.14/6.39  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 6.14/6.39  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_35])).
% 6.14/6.39  cnf(c_0_50, plain, (X3=k3_tarski(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_23]), c_0_24])).
% 6.14/6.39  cnf(c_0_51, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X1)|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_44])).
% 6.14/6.39  cnf(c_0_52, negated_conjecture, (k4_subset_1(esk4_0,esk5_0,k2_subset_1(esk4_0))!=k2_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 6.14/6.39  cnf(c_0_53, negated_conjecture, (k4_subset_1(esk4_0,esk5_0,X1)=k3_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))|~r2_hidden(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 6.14/6.39  cnf(c_0_54, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_46]), c_0_35])).
% 6.14/6.39  cnf(c_0_55, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k3_tarski(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_23]), c_0_23]), c_0_24]), c_0_24])).
% 6.14/6.39  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 6.14/6.39  cnf(c_0_57, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51])).
% 6.14/6.39  cnf(c_0_58, negated_conjecture, (k4_subset_1(esk4_0,esk5_0,esk4_0)!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_37]), c_0_37])).
% 6.14/6.39  cnf(c_0_59, negated_conjecture, (k4_subset_1(esk4_0,esk5_0,esk4_0)=k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 6.14/6.39  cnf(c_0_60, negated_conjecture, (k3_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))=X1|r2_hidden(esk2_3(esk5_0,X1,X1),esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 6.14/6.39  cnf(c_0_61, negated_conjecture, (k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))!=esk4_0), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 6.14/6.39  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk2_3(esk5_0,esk4_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_60]), c_0_55]), c_0_61])).
% 6.14/6.39  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_60]), c_0_55]), c_0_61]), ['proof']).
% 6.14/6.39  # SZS output end CNFRefutation
% 6.14/6.39  # Proof object total steps             : 64
% 6.14/6.39  # Proof object clause steps            : 37
% 6.14/6.39  # Proof object formula steps           : 27
% 6.14/6.39  # Proof object conjectures             : 14
% 6.14/6.39  # Proof object clause conjectures      : 11
% 6.14/6.39  # Proof object formula conjectures     : 3
% 6.14/6.39  # Proof object initial clauses used    : 16
% 6.14/6.39  # Proof object initial formulas used   : 13
% 6.14/6.39  # Proof object generating inferences   : 12
% 6.14/6.39  # Proof object simplifying inferences  : 25
% 6.14/6.39  # Training examples: 0 positive, 0 negative
% 6.14/6.39  # Parsed axioms                        : 13
% 6.14/6.39  # Removed by relevancy pruning/SinE    : 0
% 6.14/6.39  # Initial clauses                      : 27
% 6.14/6.39  # Removed in clause preprocessing      : 4
% 6.14/6.39  # Initial clauses in saturation        : 23
% 6.14/6.39  # Processed clauses                    : 5600
% 6.14/6.39  # ...of these trivial                  : 79
% 6.14/6.39  # ...subsumed                          : 2908
% 6.14/6.39  # ...remaining for further processing  : 2613
% 6.14/6.39  # Other redundant clauses eliminated   : 5
% 6.14/6.39  # Clauses deleted for lack of memory   : 0
% 6.14/6.39  # Backward-subsumed                    : 114
% 6.14/6.39  # Backward-rewritten                   : 9
% 6.14/6.39  # Generated clauses                    : 713591
% 6.14/6.39  # ...of the previous two non-trivial   : 697845
% 6.14/6.39  # Contextual simplify-reflections      : 10
% 6.14/6.39  # Paramodulations                      : 712782
% 6.14/6.39  # Factorizations                       : 804
% 6.14/6.39  # Equation resolutions                 : 5
% 6.14/6.39  # Propositional unsat checks           : 0
% 6.14/6.39  #    Propositional check models        : 0
% 6.14/6.39  #    Propositional check unsatisfiable : 0
% 6.14/6.39  #    Propositional clauses             : 0
% 6.14/6.39  #    Propositional clauses after purity: 0
% 6.14/6.39  #    Propositional unsat core size     : 0
% 6.14/6.39  #    Propositional preprocessing time  : 0.000
% 6.14/6.39  #    Propositional encoding time       : 0.000
% 6.14/6.39  #    Propositional solver time         : 0.000
% 6.14/6.39  #    Success case prop preproc time    : 0.000
% 6.14/6.39  #    Success case prop encoding time   : 0.000
% 6.14/6.39  #    Success case prop solver time     : 0.000
% 6.14/6.39  # Current number of processed clauses  : 2462
% 6.14/6.39  #    Positive orientable unit clauses  : 71
% 6.14/6.39  #    Positive unorientable unit clauses: 1
% 6.14/6.39  #    Negative unit clauses             : 3
% 6.14/6.39  #    Non-unit-clauses                  : 2387
% 6.14/6.39  # Current number of unprocessed clauses: 692031
% 6.14/6.39  # ...number of literals in the above   : 3496704
% 6.14/6.39  # Current number of archived formulas  : 0
% 6.14/6.39  # Current number of archived clauses   : 150
% 6.14/6.39  # Clause-clause subsumption calls (NU) : 1097501
% 6.14/6.39  # Rec. Clause-clause subsumption calls : 249397
% 6.14/6.39  # Non-unit clause-clause subsumptions  : 3024
% 6.14/6.39  # Unit Clause-clause subsumption calls : 8428
% 6.14/6.39  # Rewrite failures with RHS unbound    : 0
% 6.14/6.39  # BW rewrite match attempts            : 538
% 6.14/6.39  # BW rewrite match successes           : 6
% 6.14/6.39  # Condensation attempts                : 0
% 6.14/6.39  # Condensation successes               : 0
% 6.14/6.39  # Termbank termtop insertions          : 22111432
% 6.24/6.42  
% 6.24/6.42  # -------------------------------------------------
% 6.24/6.42  # User time                : 5.813 s
% 6.24/6.42  # System time              : 0.246 s
% 6.24/6.42  # Total time               : 6.059 s
% 6.24/6.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
