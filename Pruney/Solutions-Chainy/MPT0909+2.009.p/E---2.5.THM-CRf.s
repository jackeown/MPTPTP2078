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
% DateTime   : Thu Dec  3 11:00:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  93 expanded)
%              Number of clauses        :   24 (  38 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 373 expanded)
%              Number of equality atoms :   49 ( 217 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X6 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X6 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_mcart_1])).

fof(c_0_8,plain,(
    ! [X27,X28,X29,X30] :
      ( X27 = k1_xboole_0
      | X28 = k1_xboole_0
      | X29 = k1_xboole_0
      | ~ m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29))
      | X30 = k3_mcart_1(k5_mcart_1(X27,X28,X29,X30),k6_mcart_1(X27,X28,X29,X30),k7_mcart_1(X27,X28,X29,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_10,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,negated_conjecture,(
    ! [X36,X37,X38] :
      ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
      & ( ~ m1_subset_1(X36,esk1_0)
        | ~ m1_subset_1(X37,esk2_0)
        | ~ m1_subset_1(X38,esk3_0)
        | esk5_0 != k3_mcart_1(X36,X37,X38)
        | esk4_0 = X36 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18] :
      ( ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
      | m1_subset_1(k5_mcart_1(X15,X16,X17,X18),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))
      | m1_subset_1(k6_mcart_1(X19,X20,X21,X22),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | esk5_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_26,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))
      | m1_subset_1(k7_mcart_1(X23,X24,X25,X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 = X1
    | esk5_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_33,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk3_0)
    | ~ m1_subset_1(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_36,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.19/0.37  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.19/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.37  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 0.19/0.37  fof(dt_k6_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 0.19/0.37  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.19/0.37  fof(c_0_8, plain, ![X27, X28, X29, X30]:(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0|(~m1_subset_1(X30,k3_zfmisc_1(X27,X28,X29))|X30=k3_mcart_1(k5_mcart_1(X27,X28,X29,X30),k6_mcart_1(X27,X28,X29,X30),k7_mcart_1(X27,X28,X29,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.19/0.37  fof(c_0_9, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.37  fof(c_0_10, plain, ![X12, X13, X14]:k3_zfmisc_1(X12,X13,X14)=k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.37  fof(c_0_11, negated_conjecture, ![X36, X37, X38]:(m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&((~m1_subset_1(X36,esk1_0)|(~m1_subset_1(X37,esk2_0)|(~m1_subset_1(X38,esk3_0)|(esk5_0!=k3_mcart_1(X36,X37,X38)|esk4_0=X36))))&(((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.37  fof(c_0_12, plain, ![X15, X16, X17, X18]:(~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|m1_subset_1(k5_mcart_1(X15,X16,X17,X18),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 0.19/0.37  cnf(c_0_13, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_14, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_15, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_17, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_18, plain, ![X19, X20, X21, X22]:(~m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))|m1_subset_1(k6_mcart_1(X19,X20,X21,X22),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (esk4_0=X1|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X3,esk3_0)|esk5_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_20, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_25, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.19/0.37  cnf(c_0_26, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  fof(c_0_27, plain, ![X23, X24, X25, X26]:(~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))|m1_subset_1(k7_mcart_1(X23,X24,X25,X26),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (esk4_0=X1|esk5_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (esk4_0!=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_32, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_26, c_0_15])).
% 0.19/0.37  cnf(c_0_33, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (~m1_subset_1(k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk3_0)|~m1_subset_1(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.19/0.37  cnf(c_0_36, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_33, c_0_15])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (~m1_subset_1(k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_37]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 39
% 0.19/0.37  # Proof object clause steps            : 24
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 17
% 0.19/0.37  # Proof object clause conjectures      : 14
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 12
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 5
% 0.19/0.37  # Proof object simplifying inferences  : 16
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 12
% 0.19/0.37  # Removed in clause preprocessing      : 2
% 0.19/0.37  # Initial clauses in saturation        : 10
% 0.19/0.37  # Processed clauses                    : 26
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 25
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 1
% 0.19/0.37  # Generated clauses                    : 6
% 0.19/0.37  # ...of the previous two non-trivial   : 7
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 6
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 14
% 0.19/0.37  #    Positive orientable unit clauses  : 4
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 5
% 0.19/0.37  #    Non-unit-clauses                  : 5
% 0.19/0.37  # Current number of unprocessed clauses: 1
% 0.19/0.37  # ...number of literals in the above   : 5
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 13
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 3
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1156
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
