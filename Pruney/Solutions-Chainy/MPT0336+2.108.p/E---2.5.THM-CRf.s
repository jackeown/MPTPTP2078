%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  84 expanded)
%              Number of clauses        :   31 (  38 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 ( 230 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_10,plain,(
    ! [X21,X22] : r1_xboole_0(k4_xboole_0(X21,X22),X22) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X25,X26] :
      ( ( k4_xboole_0(X25,k1_tarski(X26)) != X25
        | ~ r2_hidden(X26,X25) )
      & ( r2_hidden(X26,X25)
        | k4_xboole_0(X25,k1_tarski(X26)) = X25 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X16,X17,X18] :
      ( ( r1_xboole_0(X16,k2_xboole_0(X17,X18))
        | ~ r1_xboole_0(X16,X17)
        | ~ r1_xboole_0(X16,X18) )
      & ( r1_xboole_0(X16,X17)
        | ~ r1_xboole_0(X16,k2_xboole_0(X17,X18)) )
      & ( r1_xboole_0(X16,X18)
        | ~ r1_xboole_0(X16,k2_xboole_0(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

fof(c_0_30,plain,(
    ! [X23,X24] :
      ( ( ~ r1_xboole_0(X23,X24)
        | k4_xboole_0(X23,X24) = X23 )
      & ( k4_xboole_0(X23,X24) != X23
        | r1_xboole_0(X23,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk5_0),X1)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_29])).

fof(c_0_33,plain,(
    ! [X13,X14,X15] :
      ( ( r1_tarski(X13,X14)
        | ~ r1_tarski(X13,k4_xboole_0(X14,X15)) )
      & ( r1_xboole_0(X13,X15)
        | ~ r1_tarski(X13,k4_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),esk3_0) = k1_tarski(esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( r1_xboole_0(X19,X20)
      | ~ r1_xboole_0(k3_xboole_0(X19,X20),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,k1_tarski(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.20/0.39  # and selection function SelectNewComplexAHP.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.39  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.39  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.20/0.39  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.39  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.39  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.39  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.20/0.39  fof(c_0_9, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.39  fof(c_0_10, plain, ![X21, X22]:r1_xboole_0(k4_xboole_0(X21,X22),X22), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.20/0.39  cnf(c_0_12, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_13, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  fof(c_0_14, plain, ![X25, X26]:((k4_xboole_0(X25,k1_tarski(X26))!=X25|~r2_hidden(X26,X25))&(r2_hidden(X26,X25)|k4_xboole_0(X25,k1_tarski(X26))=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_15, plain, ![X16, X17, X18]:((r1_xboole_0(X16,k2_xboole_0(X17,X18))|~r1_xboole_0(X16,X17)|~r1_xboole_0(X16,X18))&((r1_xboole_0(X16,X17)|~r1_xboole_0(X16,k2_xboole_0(X17,X18)))&(r1_xboole_0(X16,X18)|~r1_xboole_0(X16,k2_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.39  fof(c_0_16, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.39  fof(c_0_17, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.39  cnf(c_0_18, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.39  cnf(c_0_19, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_20, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_25, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk5_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  cnf(c_0_28, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|r1_xboole_0(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.20/0.39  fof(c_0_30, plain, ![X23, X24]:((~r1_xboole_0(X23,X24)|k4_xboole_0(X23,X24)=X23)&(k4_xboole_0(X23,X24)!=X23|r1_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k1_tarski(esk5_0),X1)|~r1_xboole_0(k2_xboole_0(X1,X2),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_29])).
% 0.20/0.39  fof(c_0_33, plain, ![X13, X14, X15]:((r1_tarski(X13,X14)|~r1_tarski(X13,k4_xboole_0(X14,X15)))&(r1_xboole_0(X13,X15)|~r1_tarski(X13,k4_xboole_0(X14,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.20/0.39  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (r1_xboole_0(k1_tarski(esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),esk3_0)=k1_tarski(esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.39  fof(c_0_38, plain, ![X19, X20]:(r1_xboole_0(X19,X20)|~r1_xboole_0(k3_xboole_0(X19,X20),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,k1_tarski(esk5_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_21])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_43])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_44])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_47]), c_0_48]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 50
% 0.20/0.39  # Proof object clause steps            : 31
% 0.20/0.39  # Proof object formula steps           : 19
% 0.20/0.39  # Proof object conjectures             : 22
% 0.20/0.39  # Proof object clause conjectures      : 19
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 13
% 0.20/0.39  # Proof object initial formulas used   : 9
% 0.20/0.39  # Proof object generating inferences   : 18
% 0.20/0.39  # Proof object simplifying inferences  : 1
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 9
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 19
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 19
% 0.20/0.39  # Processed clauses                    : 285
% 0.20/0.39  # ...of these trivial                  : 13
% 0.20/0.39  # ...subsumed                          : 109
% 0.20/0.39  # ...remaining for further processing  : 163
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 906
% 0.20/0.39  # ...of the previous two non-trivial   : 711
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 906
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 163
% 0.20/0.39  #    Positive orientable unit clauses  : 46
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 34
% 0.20/0.39  #    Non-unit-clauses                  : 83
% 0.20/0.39  # Current number of unprocessed clauses: 442
% 0.20/0.39  # ...number of literals in the above   : 724
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 0
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 603
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 565
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 53
% 0.20/0.39  # Unit Clause-clause subsumption calls : 246
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 5
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9223
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.038 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.044 s
% 0.20/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
