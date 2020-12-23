%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 148 expanded)
%              Number of clauses        :   24 (  50 expanded)
%              Number of leaves         :    4 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 (1058 expanded)
%              Number of equality atoms :  106 ( 657 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X7 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t68_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ? [X5,X6,X7] :
              ( X4 = k3_mcart_1(X5,X6,X7)
              & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                  & k6_mcart_1(X1,X2,X3,X4) = X6
                  & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X7 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_mcart_1])).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X19] :
      ( ( m1_subset_1(esk1_4(X16,X17,X18,X19),X16)
        | ~ m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( m1_subset_1(esk2_4(X16,X17,X18,X19),X17)
        | ~ m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( m1_subset_1(esk3_4(X16,X17,X18,X19),X18)
        | ~ m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X19 = k3_mcart_1(esk1_4(X16,X17,X18,X19),esk2_4(X16,X17,X18,X19),esk3_4(X16,X17,X18,X19))
        | ~ m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,negated_conjecture,(
    ! [X39,X40,X41] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X39,esk4_0)
        | ~ m1_subset_1(X40,esk5_0)
        | ~ m1_subset_1(X41,esk6_0)
        | esk8_0 != k3_mcart_1(X39,X40,X41)
        | esk7_0 = X40 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( X1 = k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33] :
      ( ( k5_mcart_1(X27,X28,X29,X30) = X31
        | X30 != k3_mcart_1(X31,X32,X33)
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | ~ m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29)) )
      & ( k6_mcart_1(X27,X28,X29,X30) = X32
        | X30 != k3_mcart_1(X31,X32,X33)
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | ~ m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29)) )
      & ( k7_mcart_1(X27,X28,X29,X30) = X33
        | X30 != k3_mcart_1(X31,X32,X33)
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | ~ m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_mcart_1])])])])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 = X2
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X5,X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( esk7_0 = X2
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_26,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k4_tarski(k4_tarski(X6,X5),X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( esk2_4(esk4_0,esk5_0,esk6_0,esk8_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_28,plain,
    ( k6_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6)) = X5
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk7_0),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk8_0) = esk7_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_31]),c_0_14]),c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t70_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 0.13/0.38  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.13/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.38  fof(t68_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t70_mcart_1])).
% 0.13/0.38  fof(c_0_5, plain, ![X16, X17, X18, X19]:((m1_subset_1(esk1_4(X16,X17,X18,X19),X16)|~m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))&((m1_subset_1(esk2_4(X16,X17,X18,X19),X17)|~m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))&((m1_subset_1(esk3_4(X16,X17,X18,X19),X18)|~m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))&(X19=k3_mcart_1(esk1_4(X16,X17,X18,X19),esk2_4(X16,X17,X18,X19),esk3_4(X16,X17,X18,X19))|~m1_subset_1(X19,k3_zfmisc_1(X16,X17,X18))|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ![X39, X40, X41]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X39,esk4_0)|(~m1_subset_1(X40,esk5_0)|(~m1_subset_1(X41,esk6_0)|(esk8_0!=k3_mcart_1(X39,X40,X41)|esk7_0=X40))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.13/0.38  cnf(c_0_8, plain, (X1=k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_9, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_10, plain, ![X27, X28, X29, X30, X31, X32, X33]:(((k5_mcart_1(X27,X28,X29,X30)=X31|X30!=k3_mcart_1(X31,X32,X33)|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0)|~m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29)))&(k6_mcart_1(X27,X28,X29,X30)=X32|X30!=k3_mcart_1(X31,X32,X33)|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0)|~m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29))))&(k7_mcart_1(X27,X28,X29,X30)=X33|X30!=k3_mcart_1(X31,X32,X33)|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0)|~m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_mcart_1])])])])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (esk7_0=X2|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_17, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_19, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_20, plain, (k6_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X5,X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (esk7_0=X2|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_11, c_0_9])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_13]), c_0_14]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_14]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=X5|X4!=k4_tarski(k4_tarski(X6,X5),X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(rw,[status(thm)],[c_0_20, c_0_9])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])])).
% 0.13/0.38  cnf(c_0_28, plain, (k6_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6))=X5|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X1,X2,X3))), inference(er,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk7_0),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(rw,[status(thm)],[c_0_22, c_0_27])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k6_mcart_1(X1,X2,X3,esk8_0)=esk7_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk8_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (esk7_0!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_13]), c_0_31]), c_0_14]), c_0_15]), c_0_16]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 33
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 9
% 0.13/0.38  # Proof object conjectures             : 18
% 0.13/0.38  # Proof object clause conjectures      : 15
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 4
% 0.13/0.38  # Proof object generating inferences   : 7
% 0.13/0.38  # Proof object simplifying inferences  : 25
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 17
% 0.13/0.38  # Processed clauses                    : 51
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 51
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 35
% 0.13/0.38  # ...of the previous two non-trivial   : 36
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 32
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 29
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 15
% 0.13/0.38  # Current number of unprocessed clauses: 19
% 0.13/0.38  # ...number of literals in the above   : 95
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 20
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 22
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 36
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2383
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
