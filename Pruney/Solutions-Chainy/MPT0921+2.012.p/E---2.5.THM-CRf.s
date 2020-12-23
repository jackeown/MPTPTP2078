%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 117 expanded)
%              Number of clauses        :   24 (  40 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 922 expanded)
%              Number of equality atoms :   82 ( 544 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
     => ( ! [X7] :
            ( m1_subset_1(X7,X1)
           => ! [X8] :
                ( m1_subset_1(X8,X2)
               => ! [X9] :
                    ( m1_subset_1(X9,X3)
                   => ! [X10] :
                        ( m1_subset_1(X10,X4)
                       => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                         => X5 = X9 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(t61_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
       => ( ! [X7] :
              ( m1_subset_1(X7,X1)
             => ! [X8] :
                  ( m1_subset_1(X8,X2)
                 => ! [X9] :
                      ( m1_subset_1(X9,X3)
                     => ! [X10] :
                          ( m1_subset_1(X10,X4)
                         => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                           => X5 = X9 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_mcart_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
      | m1_subset_1(k10_mcart_1(X11,X12,X13,X14,X15),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X47,X48,X49,X50] :
      ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
      & ( ~ m1_subset_1(X47,esk1_0)
        | ~ m1_subset_1(X48,esk2_0)
        | ~ m1_subset_1(X49,esk3_0)
        | ~ m1_subset_1(X50,esk4_0)
        | esk6_0 != k4_mcart_1(X47,X48,X49,X50)
        | esk5_0 = X49 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ~ m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19))
      | m1_subset_1(k11_mcart_1(X16,X17,X18,X19,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

cnf(c_0_13,negated_conjecture,
    ( esk5_0 = X3
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X4,esk4_0)
    | esk6_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( esk5_0 != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( ( k8_mcart_1(X36,X37,X38,X39,X40) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X40)))
        | ~ m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k9_mcart_1(X36,X37,X38,X39,X40) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X40)))
        | ~ m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k10_mcart_1(X36,X37,X38,X39,X40) = k2_mcart_1(k1_mcart_1(X40))
        | ~ m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k11_mcart_1(X36,X37,X38,X39,X40) = k2_mcart_1(X40)
        | ~ m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_18,negated_conjecture,
    ( k4_mcart_1(X1,X2,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),X3) != esk6_0
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_20,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_25,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ~ m1_subset_1(X25,k4_zfmisc_1(X21,X22,X23,X24))
      | m1_subset_1(k8_mcart_1(X21,X22,X23,X24,X25),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_26,negated_conjecture,
    ( k4_mcart_1(X1,X2,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) != esk6_0
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) = k2_mcart_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_11]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( ~ m1_subset_1(X30,k4_zfmisc_1(X26,X27,X28,X29))
      | m1_subset_1(k9_mcart_1(X26,X27,X28,X29,X30),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_30,negated_conjecture,
    ( k4_mcart_1(X1,X2,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k2_mcart_1(esk6_0)) != esk6_0
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_11])).

cnf(c_0_32,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X31,X32,X33,X34,X35] :
      ( X31 = k1_xboole_0
      | X32 = k1_xboole_0
      | X33 = k1_xboole_0
      | X34 = k1_xboole_0
      | ~ m1_subset_1(X35,k4_zfmisc_1(X31,X32,X33,X34))
      | X35 = k4_mcart_1(k8_mcart_1(X31,X32,X33,X34,X35),k9_mcart_1(X31,X32,X33,X34,X35),k10_mcart_1(X31,X32,X33,X34,X35),k11_mcart_1(X31,X32,X33,X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_34,negated_conjecture,
    ( k4_mcart_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),X1,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k2_mcart_1(esk6_0)) != esk6_0
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_11])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k4_mcart_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k2_mcart_1(esk6_0)) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_11]),c_0_27]),c_0_37]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.19/0.37  # and selection function SelectNegativeLiterals.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t81_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 0.19/0.37  fof(dt_k10_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 0.19/0.37  fof(dt_k11_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 0.19/0.37  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.19/0.37  fof(dt_k8_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 0.19/0.37  fof(dt_k9_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 0.19/0.37  fof(t60_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_mcart_1)).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t81_mcart_1])).
% 0.19/0.37  fof(c_0_8, plain, ![X11, X12, X13, X14, X15]:(~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|m1_subset_1(k10_mcart_1(X11,X12,X13,X14,X15),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ![X47, X48, X49, X50]:(m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&((~m1_subset_1(X47,esk1_0)|(~m1_subset_1(X48,esk2_0)|(~m1_subset_1(X49,esk3_0)|(~m1_subset_1(X50,esk4_0)|(esk6_0!=k4_mcart_1(X47,X48,X49,X50)|esk5_0=X49)))))&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&esk5_0!=k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.37  cnf(c_0_10, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  fof(c_0_12, plain, ![X16, X17, X18, X19, X20]:(~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19))|m1_subset_1(k11_mcart_1(X16,X17,X18,X19,X20),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (esk5_0=X3|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X4,esk4_0)|esk6_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (esk5_0!=k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_16, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_17, plain, ![X36, X37, X38, X39, X40]:((((k8_mcart_1(X36,X37,X38,X39,X40)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X40)))|~m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))&(k9_mcart_1(X36,X37,X38,X39,X40)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X40)))|~m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0)))&(k10_mcart_1(X36,X37,X38,X39,X40)=k2_mcart_1(k1_mcart_1(X40))|~m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0)))&(k11_mcart_1(X36,X37,X38,X39,X40)=k2_mcart_1(X40)|~m1_subset_1(X40,k4_zfmisc_1(X36,X37,X38,X39))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (k4_mcart_1(X1,X2,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),X3)!=esk6_0|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_11])).
% 0.19/0.37  cnf(c_0_20, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  fof(c_0_25, plain, ![X21, X22, X23, X24, X25]:(~m1_subset_1(X25,k4_zfmisc_1(X21,X22,X23,X24))|m1_subset_1(k8_mcart_1(X21,X22,X23,X24,X25),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (k4_mcart_1(X1,X2,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))!=esk6_0|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)=k2_mcart_1(esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_11]), c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.19/0.37  cnf(c_0_28, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  fof(c_0_29, plain, ![X26, X27, X28, X29, X30]:(~m1_subset_1(X30,k4_zfmisc_1(X26,X27,X28,X29))|m1_subset_1(k9_mcart_1(X26,X27,X28,X29,X30),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k4_mcart_1(X1,X2,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k2_mcart_1(esk6_0))!=esk6_0|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_11])).
% 0.19/0.37  cnf(c_0_32, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  fof(c_0_33, plain, ![X31, X32, X33, X34, X35]:(X31=k1_xboole_0|X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0|(~m1_subset_1(X35,k4_zfmisc_1(X31,X32,X33,X34))|X35=k4_mcart_1(k8_mcart_1(X31,X32,X33,X34,X35),k9_mcart_1(X31,X32,X33,X34,X35),k10_mcart_1(X31,X32,X33,X34,X35),k11_mcart_1(X31,X32,X33,X34,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (k4_mcart_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),X1,k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k2_mcart_1(esk6_0))!=esk6_0|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_11])).
% 0.19/0.37  cnf(c_0_36, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (k4_mcart_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k2_mcart_1(esk6_0))!=esk6_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_11]), c_0_27]), c_0_37]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 39
% 0.19/0.37  # Proof object clause steps            : 24
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 21
% 0.19/0.37  # Proof object clause conjectures      : 18
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 10
% 0.19/0.37  # Proof object simplifying inferences  : 12
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 65
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 11
% 0.19/0.37  # ...remaining for further processing  : 54
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 35
% 0.19/0.37  # ...of the previous two non-trivial   : 36
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 35
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
% 0.19/0.37  # Current number of processed clauses  : 36
% 0.19/0.37  #    Positive orientable unit clauses  : 9
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 6
% 0.19/0.37  #    Non-unit-clauses                  : 21
% 0.19/0.37  # Current number of unprocessed clauses: 3
% 0.19/0.37  # ...number of literals in the above   : 15
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 18
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 20
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 14
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.37  # Unit Clause-clause subsumption calls : 9
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2651
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.030 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
