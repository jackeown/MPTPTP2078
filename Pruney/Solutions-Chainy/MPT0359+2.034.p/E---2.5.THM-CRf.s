%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 199 expanded)
%              Number of clauses        :   36 (  90 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 532 expanded)
%              Number of equality atoms :   55 ( 161 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(k3_subset_1(X1,X2),X2)
        <=> X2 = k2_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t39_subset_1])).

fof(c_0_20,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X26,X25)
        | r1_tarski(X26,X24)
        | X25 != k1_zfmisc_1(X24) )
      & ( ~ r1_tarski(X27,X24)
        | r2_hidden(X27,X25)
        | X25 != k1_zfmisc_1(X24) )
      & ( ~ r2_hidden(esk3_2(X28,X29),X29)
        | ~ r1_tarski(esk3_2(X28,X29),X28)
        | X29 = k1_zfmisc_1(X28) )
      & ( r2_hidden(esk3_2(X28,X29),X29)
        | r1_tarski(esk3_2(X28,X29),X28)
        | X29 = k1_zfmisc_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X32,X31)
        | r2_hidden(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ r2_hidden(X32,X31)
        | m1_subset_1(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ m1_subset_1(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_xboole_0(X31) )
      & ( ~ v1_xboole_0(X32)
        | m1_subset_1(X32,X31)
        | ~ v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_22,plain,(
    ! [X41] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_23,plain,(
    ! [X37] : ~ v1_xboole_0(k1_zfmisc_1(X37)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_24,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
      | esk5_0 != k2_subset_1(esk4_0) )
    & ( r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
      | esk5_0 = k2_subset_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_28,plain,(
    ! [X34] : k2_subset_1(X34) = X34 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
    | esk5_0 = k2_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k3_subset_1(X2,X1))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = esk4_0
    | r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk1_2(k3_subset_1(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk1_2(k3_subset_1(esk4_0,esk5_0),X1),esk5_0)
    | r1_tarski(k3_subset_1(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_50,plain,(
    ! [X40] : k2_subset_1(X40) = k3_subset_1(X40,k1_subset_1(X40)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_51,plain,(
    ! [X33] : k1_subset_1(X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_52,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | k3_subset_1(X38,k3_subset_1(X38,X39)) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_tarski(k3_subset_1(esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_55,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)
    | esk5_0 != k2_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_58,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k3_subset_1(esk4_0,esk5_0) = k1_xboole_0
    | esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_38]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 != esk4_0
    | ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_49])])).

cnf(c_0_63,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_60]),c_0_31])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62]),c_0_63]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:31:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.38  fof(t39_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 0.20/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.20/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.38  fof(c_0_14, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_18, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1)))), inference(assume_negation,[status(cth)],[t39_subset_1])).
% 0.20/0.38  fof(c_0_20, plain, ![X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X26,X25)|r1_tarski(X26,X24)|X25!=k1_zfmisc_1(X24))&(~r1_tarski(X27,X24)|r2_hidden(X27,X25)|X25!=k1_zfmisc_1(X24)))&((~r2_hidden(esk3_2(X28,X29),X29)|~r1_tarski(esk3_2(X28,X29),X28)|X29=k1_zfmisc_1(X28))&(r2_hidden(esk3_2(X28,X29),X29)|r1_tarski(esk3_2(X28,X29),X28)|X29=k1_zfmisc_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X31, X32]:(((~m1_subset_1(X32,X31)|r2_hidden(X32,X31)|v1_xboole_0(X31))&(~r2_hidden(X32,X31)|m1_subset_1(X32,X31)|v1_xboole_0(X31)))&((~m1_subset_1(X32,X31)|v1_xboole_0(X32)|~v1_xboole_0(X31))&(~v1_xboole_0(X32)|m1_subset_1(X32,X31)|~v1_xboole_0(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.38  fof(c_0_22, plain, ![X41]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.38  fof(c_0_23, plain, ![X37]:~v1_xboole_0(k1_zfmisc_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.38  cnf(c_0_24, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_25, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_26, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  fof(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0!=k2_subset_1(esk4_0))&(r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0=k2_subset_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.38  fof(c_0_28, plain, ![X34]:k2_subset_1(X34)=X34, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_31, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_32, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_33, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_34, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0=k2_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_38, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  fof(c_0_39, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_41, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.38  cnf(c_0_42, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k3_subset_1(X2,X1))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.38  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (esk5_0=esk4_0|r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.38  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.38  cnf(c_0_47, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(esk1_2(k3_subset_1(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_42, c_0_36])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk1_2(k3_subset_1(esk4_0,esk5_0),X1),esk5_0)|r1_tarski(k3_subset_1(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  fof(c_0_50, plain, ![X40]:k2_subset_1(X40)=k3_subset_1(X40,k1_subset_1(X40)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.20/0.38  fof(c_0_51, plain, ![X33]:k1_subset_1(X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.38  fof(c_0_52, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|k3_subset_1(X38,k3_subset_1(X38,X39))=X39), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.38  cnf(c_0_53, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (esk4_0=esk5_0|r1_tarski(k3_subset_1(esk4_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.20/0.38  cnf(c_0_55, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.38  cnf(c_0_56, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)|esk5_0!=k2_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_58, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (k3_subset_1(esk4_0,esk5_0)=k1_xboole_0|esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.38  cnf(c_0_60, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_38]), c_0_56])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (esk5_0!=esk4_0|~r1_tarski(k3_subset_1(esk4_0,esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_57, c_0_38])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (esk4_0=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_49])])).
% 0.20/0.38  cnf(c_0_63, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_60]), c_0_31])])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62]), c_0_63]), c_0_46])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 65
% 0.20/0.38  # Proof object clause steps            : 36
% 0.20/0.38  # Proof object formula steps           : 29
% 0.20/0.38  # Proof object conjectures             : 13
% 0.20/0.38  # Proof object clause conjectures      : 10
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 11
% 0.20/0.38  # Proof object simplifying inferences  : 21
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 31
% 0.20/0.38  # Removed in clause preprocessing      : 3
% 0.20/0.38  # Initial clauses in saturation        : 28
% 0.20/0.38  # Processed clauses                    : 195
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 63
% 0.20/0.38  # ...remaining for further processing  : 132
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 3
% 0.20/0.38  # Backward-rewritten                   : 19
% 0.20/0.38  # Generated clauses                    : 454
% 0.20/0.38  # ...of the previous two non-trivial   : 374
% 0.20/0.38  # Contextual simplify-reflections      : 3
% 0.20/0.38  # Paramodulations                      : 445
% 0.20/0.38  # Factorizations                       : 2
% 0.20/0.38  # Equation resolutions                 : 7
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 76
% 0.20/0.38  #    Positive orientable unit clauses  : 10
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 63
% 0.20/0.38  # Current number of unprocessed clauses: 222
% 0.20/0.38  # ...number of literals in the above   : 774
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 52
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1159
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 938
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 38
% 0.20/0.38  # Unit Clause-clause subsumption calls : 250
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 14
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 7802
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.041 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.044 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
