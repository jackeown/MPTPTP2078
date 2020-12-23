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
% DateTime   : Thu Dec  3 10:47:31 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of clauses        :   27 (  35 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 155 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_setfam_1(X2,k1_tarski(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t18_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t23_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X2,X3) )
     => r1_setfam_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_setfam_1(X2,k1_tarski(X1))
       => ! [X3] :
            ( r2_hidden(X3,X2)
           => r1_tarski(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t24_setfam_1])).

fof(c_0_15,negated_conjecture,
    ( r1_setfam_1(esk4_0,k1_tarski(esk3_0))
    & r2_hidden(esk5_0,esk4_0)
    & ~ r1_tarski(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k5_enumset1(X23,X23,X24,X25,X26,X27,X28) = k4_enumset1(X23,X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35] : k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35) = k5_enumset1(X29,X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X44,X45,X47] :
      ( ( r2_hidden(esk1_3(X40,X41,X42),X41)
        | ~ r2_hidden(X42,X40)
        | ~ r1_setfam_1(X40,X41) )
      & ( r1_tarski(X42,esk1_3(X40,X41,X42))
        | ~ r2_hidden(X42,X40)
        | ~ r1_setfam_1(X40,X41) )
      & ( r2_hidden(esk2_2(X44,X45),X44)
        | r1_setfam_1(X44,X45) )
      & ( ~ r2_hidden(X47,X45)
        | ~ r1_tarski(esk2_2(X44,X45),X47)
        | r1_setfam_1(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_24,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | r1_tarski(X36,k3_tarski(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_25,plain,(
    ! [X48,X49] :
      ( ~ r1_setfam_1(X48,X49)
      | r1_tarski(k3_tarski(X48),k3_tarski(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).

fof(c_0_26,plain,(
    ! [X39] : k3_tarski(k1_zfmisc_1(X39)) = X39 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X50,X51,X52] :
      ( ~ r1_setfam_1(X50,X51)
      | ~ r1_setfam_1(X51,X52)
      | r1_setfam_1(X50,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_setfam_1])])).

cnf(c_0_28,negated_conjecture,
    ( r1_setfam_1(esk4_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X38] : k3_tarski(k1_tarski(X38)) = X38 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_37,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk2_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( r1_setfam_1(X1,X3)
    | ~ r1_setfam_1(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r1_setfam_1(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X3)
    | ~ r2_hidden(k3_tarski(X3),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r1_setfam_1(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_setfam_1(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r1_setfam_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_49,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r2_hidden(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_setfam_1(k1_zfmisc_1(X1),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_51,plain,
    ( r1_setfam_1(k1_zfmisc_1(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t24_setfam_1, conjecture, ![X1, X2]:(r1_setfam_1(X2,k1_tarski(X1))=>![X3]:(r2_hidden(X3,X2)=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 0.21/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.38  fof(d2_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,X2)&r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 0.21/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.21/0.38  fof(t18_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 0.21/0.38  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.21/0.38  fof(t23_setfam_1, axiom, ![X1, X2, X3]:((r1_setfam_1(X1,X2)&r1_setfam_1(X2,X3))=>r1_setfam_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_setfam_1)).
% 0.21/0.38  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.21/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(r1_setfam_1(X2,k1_tarski(X1))=>![X3]:(r2_hidden(X3,X2)=>r1_tarski(X3,X1)))), inference(assume_negation,[status(cth)],[t24_setfam_1])).
% 0.21/0.38  fof(c_0_15, negated_conjecture, (r1_setfam_1(esk4_0,k1_tarski(esk3_0))&(r2_hidden(esk5_0,esk4_0)&~r1_tarski(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.38  fof(c_0_16, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.38  fof(c_0_17, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_18, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.38  fof(c_0_19, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.38  fof(c_0_20, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.38  fof(c_0_21, plain, ![X23, X24, X25, X26, X27, X28]:k5_enumset1(X23,X23,X24,X25,X26,X27,X28)=k4_enumset1(X23,X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.38  fof(c_0_22, plain, ![X29, X30, X31, X32, X33, X34, X35]:k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35)=k5_enumset1(X29,X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.38  fof(c_0_23, plain, ![X40, X41, X42, X44, X45, X47]:(((r2_hidden(esk1_3(X40,X41,X42),X41)|~r2_hidden(X42,X40)|~r1_setfam_1(X40,X41))&(r1_tarski(X42,esk1_3(X40,X41,X42))|~r2_hidden(X42,X40)|~r1_setfam_1(X40,X41)))&((r2_hidden(esk2_2(X44,X45),X44)|r1_setfam_1(X44,X45))&(~r2_hidden(X47,X45)|~r1_tarski(esk2_2(X44,X45),X47)|r1_setfam_1(X44,X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).
% 0.21/0.38  fof(c_0_24, plain, ![X36, X37]:(~r2_hidden(X36,X37)|r1_tarski(X36,k3_tarski(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.21/0.38  fof(c_0_25, plain, ![X48, X49]:(~r1_setfam_1(X48,X49)|r1_tarski(k3_tarski(X48),k3_tarski(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).
% 0.21/0.38  fof(c_0_26, plain, ![X39]:k3_tarski(k1_zfmisc_1(X39))=X39, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.21/0.38  fof(c_0_27, plain, ![X50, X51, X52]:(~r1_setfam_1(X50,X51)|~r1_setfam_1(X51,X52)|r1_setfam_1(X50,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_setfam_1])])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (r1_setfam_1(esk4_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.38  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  fof(c_0_36, plain, ![X38]:k3_tarski(k1_tarski(X38))=X38, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.21/0.38  cnf(c_0_37, plain, (r1_setfam_1(X3,X2)|~r2_hidden(X1,X2)|~r1_tarski(esk2_2(X3,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_38, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.38  cnf(c_0_39, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.38  cnf(c_0_40, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  cnf(c_0_41, plain, (r1_setfam_1(X1,X3)|~r1_setfam_1(X1,X2)|~r1_setfam_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_42, negated_conjecture, (r1_setfam_1(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.21/0.38  cnf(c_0_43, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.38  cnf(c_0_44, plain, (r1_setfam_1(X1,X2)|~r2_hidden(esk2_2(X1,X2),X3)|~r2_hidden(k3_tarski(X3),X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.38  cnf(c_0_45, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_46, plain, (r1_tarski(X1,k3_tarski(X2))|~r1_setfam_1(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (r1_setfam_1(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|~r1_setfam_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.38  cnf(c_0_48, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.21/0.38  cnf(c_0_49, plain, (r1_setfam_1(X1,X2)|~r2_hidden(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_setfam_1(k1_zfmisc_1(X1),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.21/0.38  cnf(c_0_51, plain, (r1_setfam_1(k1_zfmisc_1(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (~r1_tarski(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 56
% 0.21/0.38  # Proof object clause steps            : 27
% 0.21/0.38  # Proof object formula steps           : 29
% 0.21/0.38  # Proof object conjectures             : 11
% 0.21/0.38  # Proof object clause conjectures      : 8
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 17
% 0.21/0.38  # Proof object initial formulas used   : 14
% 0.21/0.38  # Proof object generating inferences   : 8
% 0.21/0.38  # Proof object simplifying inferences  : 17
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 14
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 19
% 0.21/0.38  # Removed in clause preprocessing      : 7
% 0.21/0.38  # Initial clauses in saturation        : 12
% 0.21/0.38  # Processed clauses                    : 34
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 34
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 0
% 0.21/0.38  # Generated clauses                    : 23
% 0.21/0.38  # ...of the previous two non-trivial   : 21
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 23
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 22
% 0.21/0.38  #    Positive orientable unit clauses  : 4
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 17
% 0.21/0.38  # Current number of unprocessed clauses: 11
% 0.21/0.38  # ...number of literals in the above   : 27
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 19
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 21
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 19
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 0
% 0.21/0.38  # BW rewrite match successes           : 0
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 1385
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.026 s
% 0.21/0.38  # System time              : 0.006 s
% 0.21/0.38  # Total time               : 0.032 s
% 0.21/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
