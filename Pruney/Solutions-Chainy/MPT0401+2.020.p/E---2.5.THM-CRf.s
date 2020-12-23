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
% DateTime   : Thu Dec  3 10:47:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  66 expanded)
%              Number of clauses        :   19 (  25 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 (  99 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_setfam_1(X2,k1_tarski(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t18_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_setfam_1(X2,k1_tarski(X1))
       => ! [X3] :
            ( r2_hidden(X3,X2)
           => r1_tarski(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t24_setfam_1])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_13,plain,(
    ! [X34,X35] :
      ( ~ r1_setfam_1(X34,X35)
      | r1_tarski(k3_tarski(X34),k3_tarski(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).

fof(c_0_14,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | r1_tarski(X32,k3_tarski(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

fof(c_0_15,negated_conjecture,
    ( r1_setfam_1(esk2_0,k1_tarski(esk1_0))
    & r2_hidden(esk3_0,esk2_0)
    & ~ r1_tarski(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X16,X17,X18,X19] : k3_enumset1(X16,X16,X17,X18,X19) = k2_enumset1(X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X20,X21,X22,X23,X24] : k4_enumset1(X20,X20,X21,X22,X23,X24) = k3_enumset1(X20,X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X25,X26,X27,X28,X29,X30] : k6_enumset1(X25,X25,X25,X26,X27,X28,X29,X30) = k4_enumset1(X25,X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

fof(c_0_26,plain,(
    ! [X31] : k3_tarski(k1_tarski(X31)) = X31 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r1_setfam_1(X3,X2)
    | ~ r1_tarski(X1,k3_tarski(X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r1_setfam_1(esk2_0,k1_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(X1))
    | ~ r1_setfam_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r1_setfam_1(esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_39,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:01:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.027 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t24_setfam_1, conjecture, ![X1, X2]:(r1_setfam_1(X2,k1_tarski(X1))=>![X3]:(r2_hidden(X3,X2)=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 0.13/0.36  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.13/0.36  fof(t18_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 0.13/0.36  fof(t92_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 0.13/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.36  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.36  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.13/0.36  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.13/0.36  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(r1_setfam_1(X2,k1_tarski(X1))=>![X3]:(r2_hidden(X3,X2)=>r1_tarski(X3,X1)))), inference(assume_negation,[status(cth)],[t24_setfam_1])).
% 0.13/0.36  fof(c_0_12, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.13/0.36  fof(c_0_13, plain, ![X34, X35]:(~r1_setfam_1(X34,X35)|r1_tarski(k3_tarski(X34),k3_tarski(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).
% 0.13/0.36  fof(c_0_14, plain, ![X32, X33]:(~r2_hidden(X32,X33)|r1_tarski(X32,k3_tarski(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).
% 0.13/0.36  fof(c_0_15, negated_conjecture, (r1_setfam_1(esk2_0,k1_tarski(esk1_0))&(r2_hidden(esk3_0,esk2_0)&~r1_tarski(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.36  cnf(c_0_16, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  cnf(c_0_17, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  fof(c_0_20, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.36  fof(c_0_21, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  fof(c_0_22, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.36  fof(c_0_23, plain, ![X16, X17, X18, X19]:k3_enumset1(X16,X16,X17,X18,X19)=k2_enumset1(X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.36  fof(c_0_24, plain, ![X20, X21, X22, X23, X24]:k4_enumset1(X20,X20,X21,X22,X23,X24)=k3_enumset1(X20,X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.36  fof(c_0_25, plain, ![X25, X26, X27, X28, X29, X30]:k6_enumset1(X25,X25,X25,X26,X27,X28,X29,X30)=k4_enumset1(X25,X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.13/0.36  fof(c_0_26, plain, ![X31]:k3_tarski(k1_tarski(X31))=X31, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.13/0.36  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(X2))|~r1_setfam_1(X3,X2)|~r1_tarski(X1,k3_tarski(X3))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.36  cnf(c_0_29, negated_conjecture, (r1_setfam_1(esk2_0,k1_tarski(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.36  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.36  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.36  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.36  cnf(c_0_36, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.36  cnf(c_0_37, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(X1))|~r1_setfam_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (r1_setfam_1(esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.13/0.36  cnf(c_0_39, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (~r1_tarski(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 42
% 0.13/0.36  # Proof object clause steps            : 19
% 0.13/0.36  # Proof object formula steps           : 23
% 0.13/0.36  # Proof object conjectures             : 10
% 0.13/0.36  # Proof object clause conjectures      : 7
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 13
% 0.13/0.36  # Proof object initial formulas used   : 11
% 0.13/0.36  # Proof object generating inferences   : 4
% 0.13/0.36  # Proof object simplifying inferences  : 14
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 11
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 13
% 0.13/0.36  # Removed in clause preprocessing      : 6
% 0.13/0.36  # Initial clauses in saturation        : 7
% 0.13/0.36  # Processed clauses                    : 19
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 19
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 11
% 0.13/0.36  # ...of the previous two non-trivial   : 10
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 11
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 12
% 0.13/0.36  #    Positive orientable unit clauses  : 4
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 7
% 0.13/0.36  # Current number of unprocessed clauses: 5
% 0.13/0.36  # ...number of literals in the above   : 13
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 13
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 4
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 4
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 800
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.027 s
% 0.13/0.36  # System time              : 0.004 s
% 0.13/0.36  # Total time               : 0.031 s
% 0.13/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
