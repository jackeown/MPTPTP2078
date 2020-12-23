%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  55 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 340 expanded)
%              Number of equality atoms :   47 ( 191 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,negated_conjecture,(
    ! [X34,X35,X36] :
      ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
      & ( ~ m1_subset_1(X34,esk1_0)
        | ~ m1_subset_1(X35,esk2_0)
        | ~ m1_subset_1(X36,esk3_0)
        | esk5_0 != k3_mcart_1(X34,X35,X36)
        | esk4_0 = X34 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ m1_subset_1(X20,k3_zfmisc_1(X17,X18,X19))
      | m1_subset_1(k7_mcart_1(X17,X18,X19,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_8,negated_conjecture,
    ( esk4_0 = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | esk5_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ m1_subset_1(X16,k3_zfmisc_1(X13,X14,X15))
      | m1_subset_1(k6_mcart_1(X13,X14,X15,X16),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_11,negated_conjecture,
    ( esk4_0 = X1
    | esk5_0 != k3_mcart_1(X1,X2,k7_mcart_1(X3,X4,esk3_0,X5))
    | ~ m1_subset_1(X5,k3_zfmisc_1(X3,X4,esk3_0))
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X9,X10,X11,X12] :
      ( ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
      | m1_subset_1(k5_mcart_1(X9,X10,X11,X12),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 = X1
    | esk5_0 != k3_mcart_1(X1,k6_mcart_1(X2,esk2_0,X3,X4),k7_mcart_1(X5,X6,esk3_0,X7))
    | ~ m1_subset_1(X7,k3_zfmisc_1(X5,X6,esk3_0))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X2,esk2_0,X3))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( esk4_0 = k5_mcart_1(esk1_0,X1,X2,X3)
    | esk5_0 != k3_mcart_1(k5_mcart_1(esk1_0,X1,X2,X3),k6_mcart_1(X4,esk2_0,X5,X6),k7_mcart_1(X7,X8,esk3_0,X9))
    | ~ m1_subset_1(X9,k3_zfmisc_1(X7,X8,esk3_0))
    | ~ m1_subset_1(X6,k3_zfmisc_1(X4,esk2_0,X5))
    | ~ m1_subset_1(X3,k3_zfmisc_1(esk1_0,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X24] :
      ( X21 = k1_xboole_0
      | X22 = k1_xboole_0
      | X23 = k1_xboole_0
      | ~ m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))
      | X24 = k3_mcart_1(k5_mcart_1(X21,X22,X23,X24),k6_mcart_1(X21,X22,X23,X24),k7_mcart_1(X21,X22,X23,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 = k5_mcart_1(esk1_0,X1,X2,X3)
    | k3_mcart_1(k5_mcart_1(esk1_0,X1,X2,X3),k6_mcart_1(X4,esk2_0,X5,X6),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)) != esk5_0
    | ~ m1_subset_1(X6,k3_zfmisc_1(X4,esk2_0,X5))
    | ~ m1_subset_1(X3,k3_zfmisc_1(esk1_0,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 = k5_mcart_1(esk1_0,X1,X2,X3)
    | k3_mcart_1(k5_mcart_1(esk1_0,X1,X2,X3),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)) != esk5_0
    | ~ m1_subset_1(X3,k3_zfmisc_1(esk1_0,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_25])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.19/0.38  # and selection function SelectVGNonCR.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.026 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.19/0.38  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.19/0.38  fof(dt_k6_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 0.19/0.38  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 0.19/0.38  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.19/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.19/0.38  fof(c_0_6, negated_conjecture, ![X34, X35, X36]:(m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&((~m1_subset_1(X34,esk1_0)|(~m1_subset_1(X35,esk2_0)|(~m1_subset_1(X36,esk3_0)|(esk5_0!=k3_mcart_1(X34,X35,X36)|esk4_0=X34))))&(((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.19/0.38  fof(c_0_7, plain, ![X17, X18, X19, X20]:(~m1_subset_1(X20,k3_zfmisc_1(X17,X18,X19))|m1_subset_1(k7_mcart_1(X17,X18,X19,X20),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.19/0.38  cnf(c_0_8, negated_conjecture, (esk4_0=X1|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X3,esk3_0)|esk5_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_9, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  fof(c_0_10, plain, ![X13, X14, X15, X16]:(~m1_subset_1(X16,k3_zfmisc_1(X13,X14,X15))|m1_subset_1(k6_mcart_1(X13,X14,X15,X16),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (esk4_0=X1|esk5_0!=k3_mcart_1(X1,X2,k7_mcart_1(X3,X4,esk3_0,X5))|~m1_subset_1(X5,k3_zfmisc_1(X3,X4,esk3_0))|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.38  cnf(c_0_12, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_13, plain, ![X9, X10, X11, X12]:(~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|m1_subset_1(k5_mcart_1(X9,X10,X11,X12),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (esk4_0=X1|esk5_0!=k3_mcart_1(X1,k6_mcart_1(X2,esk2_0,X3,X4),k7_mcart_1(X5,X6,esk3_0,X7))|~m1_subset_1(X7,k3_zfmisc_1(X5,X6,esk3_0))|~m1_subset_1(X4,k3_zfmisc_1(X2,esk2_0,X3))|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.38  cnf(c_0_15, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (esk4_0=k5_mcart_1(esk1_0,X1,X2,X3)|esk5_0!=k3_mcart_1(k5_mcart_1(esk1_0,X1,X2,X3),k6_mcart_1(X4,esk2_0,X5,X6),k7_mcart_1(X7,X8,esk3_0,X9))|~m1_subset_1(X9,k3_zfmisc_1(X7,X8,esk3_0))|~m1_subset_1(X6,k3_zfmisc_1(X4,esk2_0,X5))|~m1_subset_1(X3,k3_zfmisc_1(esk1_0,X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  fof(c_0_18, plain, ![X21, X22, X23, X24]:(X21=k1_xboole_0|X22=k1_xboole_0|X23=k1_xboole_0|(~m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))|X24=k3_mcart_1(k5_mcart_1(X21,X22,X23,X24),k6_mcart_1(X21,X22,X23,X24),k7_mcart_1(X21,X22,X23,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (esk4_0=k5_mcart_1(esk1_0,X1,X2,X3)|k3_mcart_1(k5_mcart_1(esk1_0,X1,X2,X3),k6_mcart_1(X4,esk2_0,X5,X6),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0))!=esk5_0|~m1_subset_1(X6,k3_zfmisc_1(X4,esk2_0,X5))|~m1_subset_1(X3,k3_zfmisc_1(esk1_0,X1,X2))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_20, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (esk4_0=k5_mcart_1(esk1_0,X1,X2,X3)|k3_mcart_1(k5_mcart_1(esk1_0,X1,X2,X3),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0))!=esk5_0|~m1_subset_1(X3,k3_zfmisc_1(esk1_0,X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_21]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (esk4_0!=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_25])]), c_0_26]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 28
% 0.19/0.38  # Proof object clause steps            : 17
% 0.19/0.38  # Proof object formula steps           : 11
% 0.19/0.38  # Proof object conjectures             : 16
% 0.19/0.38  # Proof object clause conjectures      : 13
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 5
% 0.19/0.38  # Proof object generating inferences   : 7
% 0.19/0.38  # Proof object simplifying inferences  : 6
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 13
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 13
% 0.19/0.38  # Processed clauses                    : 68
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 68
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 138
% 0.19/0.38  # ...of the previous two non-trivial   : 134
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 138
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 55
% 0.19/0.38  #    Positive orientable unit clauses  : 5
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 46
% 0.19/0.38  # Current number of unprocessed clauses: 92
% 0.19/0.38  # ...number of literals in the above   : 451
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 13
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 406
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 16
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 5
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5497
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
