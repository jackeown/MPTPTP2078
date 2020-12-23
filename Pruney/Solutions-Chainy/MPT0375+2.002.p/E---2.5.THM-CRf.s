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
% DateTime   : Thu Dec  3 10:46:53 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   51 (  92 expanded)
%              Number of clauses        :   26 (  35 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 215 expanded)
%              Number of equality atoms :   37 (  77 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t57_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ( X1 != k1_xboole_0
               => m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t56_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ( X1 != k1_xboole_0
           => m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(c_0_12,plain,(
    ! [X8,X9,X10] : k1_enumset1(X8,X9,X10) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_13,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X37,X38] : k3_tarski(k2_tarski(X37,X38)) = k2_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_18,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_19,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_20,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k4_subset_1(X42,X43,X44) = k2_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( X1 != k1_xboole_0
                 => m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_subset_1])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,esk1_0)
    & m1_subset_1(esk4_0,esk1_0)
    & esk1_0 != k1_xboole_0
    & ~ m1_subset_1(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_32,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
      | m1_subset_1(k4_subset_1(X39,X40,X41),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k4_subset_1(X4,k2_tarski(X1,X1),k2_tarski(X2,X3))
    | ~ m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_38,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X46,X45)
      | ~ m1_subset_1(X47,X45)
      | X45 = k1_xboole_0
      | m1_subset_1(k2_tarski(X46,X47),k1_zfmisc_1(X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_subset_1])])])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_40,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k2_tarski(X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(k2_tarski(esk2_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_tarski(X1,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk2_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_tarski(X1,esk2_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:59:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.54/0.71  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.54/0.71  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.54/0.71  #
% 0.54/0.71  # Preprocessing time       : 0.027 s
% 0.54/0.71  # Presaturation interreduction done
% 0.54/0.71  
% 0.54/0.71  # Proof found!
% 0.54/0.71  # SZS status Theorem
% 0.54/0.71  # SZS output start CNFRefutation
% 0.54/0.71  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.54/0.71  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.54/0.71  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.54/0.71  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.54/0.71  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.54/0.71  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.54/0.71  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.54/0.71  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.54/0.71  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.54/0.71  fof(t57_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_subset_1)).
% 0.54/0.71  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.54/0.71  fof(t56_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_subset_1)).
% 0.54/0.71  fof(c_0_12, plain, ![X8, X9, X10]:k1_enumset1(X8,X9,X10)=k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.54/0.71  fof(c_0_13, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.54/0.71  fof(c_0_14, plain, ![X37, X38]:k3_tarski(k2_tarski(X37,X38))=k2_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.54/0.71  fof(c_0_15, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.54/0.71  fof(c_0_16, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.54/0.71  fof(c_0_17, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.54/0.71  fof(c_0_18, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.54/0.71  fof(c_0_19, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.54/0.71  fof(c_0_20, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|~m1_subset_1(X44,k1_zfmisc_1(X42))|k4_subset_1(X42,X43,X44)=k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.54/0.71  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1))))))), inference(assume_negation,[status(cth)],[t57_subset_1])).
% 0.54/0.71  cnf(c_0_22, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.54/0.71  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.54/0.71  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.54/0.71  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.54/0.71  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.71  cnf(c_0_27, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.71  cnf(c_0_28, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.71  cnf(c_0_29, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.54/0.71  cnf(c_0_30, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.71  fof(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)&(m1_subset_1(esk3_0,esk1_0)&(m1_subset_1(esk4_0,esk1_0)&(esk1_0!=k1_xboole_0&~m1_subset_1(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.54/0.71  fof(c_0_32, plain, ![X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|~m1_subset_1(X41,k1_zfmisc_1(X39))|m1_subset_1(k4_subset_1(X39,X40,X41),k1_zfmisc_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.54/0.71  cnf(c_0_33, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.54/0.71  cnf(c_0_34, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_30, c_0_24])).
% 0.54/0.71  cnf(c_0_35, negated_conjecture, (~m1_subset_1(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.71  cnf(c_0_36, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.54/0.71  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k4_subset_1(X4,k2_tarski(X1,X1),k2_tarski(X2,X3))|~m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.54/0.71  fof(c_0_38, plain, ![X45, X46, X47]:(~m1_subset_1(X46,X45)|(~m1_subset_1(X47,X45)|(X45=k1_xboole_0|m1_subset_1(k2_tarski(X46,X47),k1_zfmisc_1(X45))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_subset_1])])])).
% 0.54/0.71  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.54/0.71  cnf(c_0_40, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.54/0.71  cnf(c_0_41, plain, (X2=k1_xboole_0|m1_subset_1(k2_tarski(X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)|~m1_subset_1(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.71  cnf(c_0_43, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.71  cnf(c_0_44, negated_conjecture, (~m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(esk1_0))|~m1_subset_1(k2_tarski(esk2_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.54/0.71  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_tarski(X1,esk4_0),k1_zfmisc_1(esk1_0))|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.54/0.71  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.71  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.71  cnf(c_0_48, negated_conjecture, (~m1_subset_1(k2_tarski(esk2_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.54/0.71  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_tarski(X1,esk2_0),k1_zfmisc_1(esk1_0))|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_43])).
% 0.54/0.71  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_47])]), ['proof']).
% 0.54/0.71  # SZS output end CNFRefutation
% 0.54/0.71  # Proof object total steps             : 51
% 0.54/0.71  # Proof object clause steps            : 26
% 0.54/0.71  # Proof object formula steps           : 25
% 0.54/0.71  # Proof object conjectures             : 14
% 0.54/0.71  # Proof object clause conjectures      : 11
% 0.54/0.71  # Proof object formula conjectures     : 3
% 0.54/0.71  # Proof object initial clauses used    : 16
% 0.54/0.71  # Proof object initial formulas used   : 12
% 0.54/0.71  # Proof object generating inferences   : 7
% 0.54/0.71  # Proof object simplifying inferences  : 19
% 0.54/0.71  # Training examples: 0 positive, 0 negative
% 0.54/0.71  # Parsed axioms                        : 13
% 0.54/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.71  # Initial clauses                      : 17
% 0.54/0.71  # Removed in clause preprocessing      : 7
% 0.54/0.71  # Initial clauses in saturation        : 10
% 0.54/0.71  # Processed clauses                    : 757
% 0.54/0.71  # ...of these trivial                  : 0
% 0.54/0.71  # ...subsumed                          : 1
% 0.54/0.71  # ...remaining for further processing  : 756
% 0.54/0.71  # Other redundant clauses eliminated   : 0
% 0.54/0.71  # Clauses deleted for lack of memory   : 0
% 0.54/0.71  # Backward-subsumed                    : 65
% 0.54/0.71  # Backward-rewritten                   : 0
% 0.54/0.71  # Generated clauses                    : 37495
% 0.54/0.71  # ...of the previous two non-trivial   : 37494
% 0.54/0.71  # Contextual simplify-reflections      : 0
% 0.54/0.71  # Paramodulations                      : 37495
% 0.54/0.71  # Factorizations                       : 0
% 0.54/0.71  # Equation resolutions                 : 0
% 0.54/0.71  # Propositional unsat checks           : 0
% 0.54/0.71  #    Propositional check models        : 0
% 0.54/0.71  #    Propositional check unsatisfiable : 0
% 0.54/0.71  #    Propositional clauses             : 0
% 0.54/0.71  #    Propositional clauses after purity: 0
% 0.54/0.71  #    Propositional unsat core size     : 0
% 0.54/0.71  #    Propositional preprocessing time  : 0.000
% 0.54/0.71  #    Propositional encoding time       : 0.000
% 0.54/0.71  #    Propositional solver time         : 0.000
% 0.54/0.71  #    Success case prop preproc time    : 0.000
% 0.54/0.71  #    Success case prop encoding time   : 0.000
% 0.54/0.71  #    Success case prop solver time     : 0.000
% 0.54/0.71  # Current number of processed clauses  : 681
% 0.54/0.71  #    Positive orientable unit clauses  : 4
% 0.54/0.71  #    Positive unorientable unit clauses: 1
% 0.54/0.71  #    Negative unit clauses             : 3
% 0.54/0.71  #    Non-unit-clauses                  : 673
% 0.54/0.71  # Current number of unprocessed clauses: 36757
% 0.54/0.71  # ...number of literals in the above   : 123830
% 0.54/0.71  # Current number of archived formulas  : 0
% 0.54/0.71  # Current number of archived clauses   : 82
% 0.54/0.71  # Clause-clause subsumption calls (NU) : 140509
% 0.54/0.71  # Rec. Clause-clause subsumption calls : 48123
% 0.54/0.71  # Non-unit clause-clause subsumptions  : 65
% 0.54/0.71  # Unit Clause-clause subsumption calls : 2
% 0.54/0.71  # Rewrite failures with RHS unbound    : 0
% 0.54/0.71  # BW rewrite match attempts            : 2
% 0.54/0.71  # BW rewrite match successes           : 2
% 0.54/0.71  # Condensation attempts                : 0
% 0.54/0.71  # Condensation successes               : 0
% 0.54/0.71  # Termbank termtop insertions          : 1378897
% 0.54/0.71  
% 0.54/0.71  # -------------------------------------------------
% 0.54/0.71  # User time                : 0.359 s
% 0.54/0.71  # System time              : 0.023 s
% 0.54/0.71  # Total time               : 0.382 s
% 0.54/0.71  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
