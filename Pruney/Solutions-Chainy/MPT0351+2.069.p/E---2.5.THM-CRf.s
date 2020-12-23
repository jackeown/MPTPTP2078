%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 104 expanded)
%              Number of clauses        :   32 (  43 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 191 expanded)
%              Number of equality atoms :   51 (  85 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

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

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t28_subset_1])).

fof(c_0_18,plain,(
    ! [X43,X44,X45,X47,X48,X49,X50,X52] :
      ( ( r2_hidden(X45,esk2_3(X43,X44,X45))
        | ~ r2_hidden(X45,X44)
        | X44 != k3_tarski(X43) )
      & ( r2_hidden(esk2_3(X43,X44,X45),X43)
        | ~ r2_hidden(X45,X44)
        | X44 != k3_tarski(X43) )
      & ( ~ r2_hidden(X47,X48)
        | ~ r2_hidden(X48,X43)
        | r2_hidden(X47,X44)
        | X44 != k3_tarski(X43) )
      & ( ~ r2_hidden(esk3_2(X49,X50),X50)
        | ~ r2_hidden(esk3_2(X49,X50),X52)
        | ~ r2_hidden(X52,X49)
        | X50 = k3_tarski(X49) )
      & ( r2_hidden(esk3_2(X49,X50),esk4_2(X49,X50))
        | r2_hidden(esk3_2(X49,X50),X50)
        | X50 = k3_tarski(X49) )
      & ( r2_hidden(esk4_2(X49,X50),X49)
        | r2_hidden(esk3_2(X49,X50),X50)
        | X50 = k3_tarski(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X57,X58] :
      ( ( ~ m1_subset_1(X58,X57)
        | r2_hidden(X58,X57)
        | v1_xboole_0(X57) )
      & ( ~ r2_hidden(X58,X57)
        | m1_subset_1(X58,X57)
        | v1_xboole_0(X57) )
      & ( ~ m1_subset_1(X58,X57)
        | v1_xboole_0(X58)
        | ~ v1_xboole_0(X57) )
      & ( ~ v1_xboole_0(X58)
        | m1_subset_1(X58,X57)
        | ~ v1_xboole_0(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0)) != k2_subset_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_21,plain,(
    ! [X61] : ~ v1_xboole_0(k1_zfmisc_1(X61)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_22,plain,(
    ! [X54,X55] : k3_tarski(k2_tarski(X54,X55)) = k2_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X56] : k3_tarski(k1_zfmisc_1(X56)) = X56 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X62,X63,X64] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(X62))
      | ~ m1_subset_1(X64,k1_zfmisc_1(X62))
      | k4_subset_1(X62,X63,X64) = k2_xboole_0(X63,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_34,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_35,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_36,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X60] : m1_subset_1(k2_subset_1(X60),k1_zfmisc_1(X60)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_49,plain,(
    ! [X59] : k2_subset_1(X59) = X59 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_50,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),esk5_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,X1)) = k4_subset_1(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_26])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0)) != k2_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk5_0)) = k4_subset_1(esk5_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,esk5_0) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_55]),c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.13/0.38  # and selection function SelectNegativeLiterals.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t28_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 0.13/0.38  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.13/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.13/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.13/0.38  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t28_subset_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X43, X44, X45, X47, X48, X49, X50, X52]:((((r2_hidden(X45,esk2_3(X43,X44,X45))|~r2_hidden(X45,X44)|X44!=k3_tarski(X43))&(r2_hidden(esk2_3(X43,X44,X45),X43)|~r2_hidden(X45,X44)|X44!=k3_tarski(X43)))&(~r2_hidden(X47,X48)|~r2_hidden(X48,X43)|r2_hidden(X47,X44)|X44!=k3_tarski(X43)))&((~r2_hidden(esk3_2(X49,X50),X50)|(~r2_hidden(esk3_2(X49,X50),X52)|~r2_hidden(X52,X49))|X50=k3_tarski(X49))&((r2_hidden(esk3_2(X49,X50),esk4_2(X49,X50))|r2_hidden(esk3_2(X49,X50),X50)|X50=k3_tarski(X49))&(r2_hidden(esk4_2(X49,X50),X49)|r2_hidden(esk3_2(X49,X50),X50)|X50=k3_tarski(X49))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X57, X58]:(((~m1_subset_1(X58,X57)|r2_hidden(X58,X57)|v1_xboole_0(X57))&(~r2_hidden(X58,X57)|m1_subset_1(X58,X57)|v1_xboole_0(X57)))&((~m1_subset_1(X58,X57)|v1_xboole_0(X58)|~v1_xboole_0(X57))&(~v1_xboole_0(X58)|m1_subset_1(X58,X57)|~v1_xboole_0(X57)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0))!=k2_subset_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X61]:~v1_xboole_0(k1_zfmisc_1(X61)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.13/0.38  fof(c_0_22, plain, ![X54, X55]:k3_tarski(k2_tarski(X54,X55))=k2_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.38  fof(c_0_23, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_27, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_28, plain, ![X56]:k3_tarski(k1_zfmisc_1(X56))=X56, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.13/0.38  fof(c_0_29, plain, ![X62, X63, X64]:(~m1_subset_1(X63,k1_zfmisc_1(X62))|~m1_subset_1(X64,k1_zfmisc_1(X62))|k4_subset_1(X62,X63,X64)=k2_xboole_0(X63,X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.13/0.38  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  fof(c_0_32, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_33, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_34, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_35, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_36, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.13/0.38  cnf(c_0_39, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  fof(c_0_40, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_41, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_42, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_46, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  fof(c_0_48, plain, ![X60]:m1_subset_1(k2_subset_1(X60),k1_zfmisc_1(X60)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.38  fof(c_0_49, plain, ![X59]:k2_subset_1(X59)=X59, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.38  fof(c_0_50, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.13/0.38  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_53, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.13/0.38  cnf(c_0_54, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_55, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.38  cnf(c_0_56, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.38  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),esk5_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,X1))=k4_subset_1(esk5_0,esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_53, c_0_26])).
% 0.13/0.38  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0))!=k2_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_62, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk5_0))=k4_subset_1(esk5_0,esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,esk5_0)!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_55]), c_0_55])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 67
% 0.13/0.38  # Proof object clause steps            : 32
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 20
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 8
% 0.13/0.38  # Initial clauses in saturation        : 20
% 0.13/0.38  # Processed clauses                    : 98
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 11
% 0.13/0.38  # ...remaining for further processing  : 87
% 0.13/0.38  # Other redundant clauses eliminated   : 8
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 295
% 0.13/0.38  # ...of the previous two non-trivial   : 254
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 268
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 27
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 87
% 0.13/0.38  #    Positive orientable unit clauses  : 18
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 67
% 0.13/0.38  # Current number of unprocessed clauses: 176
% 0.13/0.38  # ...number of literals in the above   : 463
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 8
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 263
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 241
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.38  # Unit Clause-clause subsumption calls : 51
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 18
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6820
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
