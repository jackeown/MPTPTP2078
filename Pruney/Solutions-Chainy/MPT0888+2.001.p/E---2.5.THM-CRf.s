%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 238 expanded)
%              Number of clauses        :   21 (  81 expanded)
%              Number of leaves         :    3 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 (1143 expanded)
%              Number of equality atoms :  103 ( 889 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(t47_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ? [X5,X6,X7] :
                ( X4 = k3_mcart_1(X5,X6,X7)
                & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                    & k6_mcart_1(X1,X2,X3,X4) = X6
                    & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

fof(l44_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ! [X5] :
                ( m1_subset_1(X5,X1)
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ! [X7] :
                        ( m1_subset_1(X7,X3)
                       => X4 != k3_mcart_1(X5,X6,X7) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_mcart_1])).

fof(c_0_4,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( k5_mcart_1(X15,X16,X17,X18) = X19
        | X18 != k3_mcart_1(X19,X20,X21)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( k6_mcart_1(X15,X16,X17,X18) = X20
        | X18 != k3_mcart_1(X19,X20,X21)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( k7_mcart_1(X15,X16,X17,X18) = X21
        | X18 != k3_mcart_1(X19,X20,X21)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_mcart_1])])])])).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11] :
      ( ( m1_subset_1(esk1_4(X8,X9,X10,X11),X8)
        | ~ m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( m1_subset_1(esk2_4(X8,X9,X10,X11),X9)
        | ~ m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( m1_subset_1(esk3_4(X8,X9,X10,X11),X10)
        | ~ m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X11 = k3_mcart_1(esk1_4(X8,X9,X10,X11),esk2_4(X8,X9,X10,X11),esk3_4(X8,X9,X10,X11))
        | ~ m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & esk7_0 != k3_mcart_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X5,X6,X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( X1 = k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k3_mcart_1(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0),esk3_4(esk4_0,esk5_0,esk6_0,esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk7_0) = esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X5,X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( esk1_4(esk4_0,esk5_0,esk6_0,esk7_0) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_18,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X7,X5)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X5
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0),esk3_4(esk4_0,esk5_0,esk6_0,esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_17])).

cnf(c_0_21,plain,
    ( k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk7_0) = esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk7_0) = esk3_4(esk4_0,esk5_0,esk6_0,esk7_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( esk2_4(esk4_0,esk5_0,esk6_0,esk7_0) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( esk3_4(esk4_0,esk5_0,esk6_0,esk7_0) = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( esk7_0 != k3_mcart_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_24]),c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t48_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.20/0.38  fof(t47_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_mcart_1)).
% 0.20/0.38  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.20/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t48_mcart_1])).
% 0.20/0.38  fof(c_0_4, plain, ![X15, X16, X17, X18, X19, X20, X21]:(((k5_mcart_1(X15,X16,X17,X18)=X19|X18!=k3_mcart_1(X19,X20,X21)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&(k6_mcart_1(X15,X16,X17,X18)=X20|X18!=k3_mcart_1(X19,X20,X21)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0)))&(k7_mcart_1(X15,X16,X17,X18)=X21|X18!=k3_mcart_1(X19,X20,X21)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_mcart_1])])])])).
% 0.20/0.38  fof(c_0_5, plain, ![X8, X9, X10, X11]:((m1_subset_1(esk1_4(X8,X9,X10,X11),X8)|~m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))|(X8=k1_xboole_0|X9=k1_xboole_0|X10=k1_xboole_0))&((m1_subset_1(esk2_4(X8,X9,X10,X11),X9)|~m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))|(X8=k1_xboole_0|X9=k1_xboole_0|X10=k1_xboole_0))&((m1_subset_1(esk3_4(X8,X9,X10,X11),X10)|~m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))|(X8=k1_xboole_0|X9=k1_xboole_0|X10=k1_xboole_0))&(X11=k3_mcart_1(esk1_4(X8,X9,X10,X11),esk2_4(X8,X9,X10,X11),esk3_4(X8,X9,X10,X11))|~m1_subset_1(X11,k3_zfmisc_1(X8,X9,X10))|(X8=k1_xboole_0|X9=k1_xboole_0|X10=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.20/0.38  fof(c_0_6, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&esk7_0!=k3_mcart_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.20/0.38  cnf(c_0_7, plain, (k5_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X5,X6,X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_8, plain, (X1=k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_10, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_13, plain, (k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3))), inference(er,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (k3_mcart_1(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0),esk3_4(esk4_0,esk5_0,esk6_0,esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (k5_mcart_1(X1,X2,X3,esk7_0)=esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.38  cnf(c_0_16, plain, (k6_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X5,X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.20/0.38  cnf(c_0_18, plain, (k7_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X7,X5)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_19, plain, (k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X5|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (k3_mcart_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0),esk3_4(esk4_0,esk5_0,esk6_0,esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_14, c_0_17])).
% 0.20/0.38  cnf(c_0_21, plain, (k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X6|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3))), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k6_mcart_1(X1,X2,X3,esk7_0)=esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (k7_mcart_1(X1,X2,X3,esk7_0)=esk3_4(esk4_0,esk5_0,esk6_0,esk7_0)|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (esk3_4(esk4_0,esk5_0,esk6_0,esk7_0)=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (esk7_0!=k3_mcart_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_24]), c_0_25]), c_0_26]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 28
% 0.20/0.38  # Proof object clause steps            : 21
% 0.20/0.38  # Proof object formula steps           : 7
% 0.20/0.38  # Proof object conjectures             : 17
% 0.20/0.38  # Proof object clause conjectures      : 14
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 9
% 0.20/0.38  # Proof object initial formulas used   : 3
% 0.20/0.38  # Proof object generating inferences   : 7
% 0.20/0.38  # Proof object simplifying inferences  : 19
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 3
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 12
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 12
% 0.20/0.38  # Processed clauses                    : 45
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 1
% 0.20/0.38  # ...remaining for further processing  : 43
% 0.20/0.38  # Other redundant clauses eliminated   : 3
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 8
% 0.20/0.38  # Generated clauses                    : 16
% 0.20/0.38  # ...of the previous two non-trivial   : 24
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 13
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 3
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
% 0.20/0.38  # Current number of processed clauses  : 20
% 0.20/0.38  #    Positive orientable unit clauses  : 7
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 9
% 0.20/0.38  # Current number of unprocessed clauses: 1
% 0.20/0.38  # ...number of literals in the above   : 5
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 20
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 17
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 20
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 3
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1385
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.033 s
% 0.20/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
