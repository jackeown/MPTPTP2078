%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:07 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (1019 expanded)
%              Number of clauses        :   37 ( 446 expanded)
%              Number of leaves         :    9 ( 250 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 (2595 expanded)
%              Number of equality atoms :   79 (1200 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_11,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( ~ r1_xboole_0(X11,X12)
        | k3_xboole_0(X11,X12) = k1_xboole_0 )
      & ( k3_xboole_0(X11,X12) != k1_xboole_0
        | r1_xboole_0(X11,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_13,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r1_xboole_0(X31,X32)
        | r1_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X34)) )
      & ( ~ r1_xboole_0(X33,X34)
        | r1_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X35,X36,X37,X38] :
      ( ( X35 = X37
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | k2_zfmisc_1(X35,X36) != k2_zfmisc_1(X37,X38) )
      & ( X36 = X38
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | k2_zfmisc_1(X35,X36) != k2_zfmisc_1(X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30] : k2_zfmisc_1(k3_xboole_0(X27,X28),k3_xboole_0(X29,X30)) = k3_xboole_0(k2_zfmisc_1(X27,X29),k2_zfmisc_1(X28,X30)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k1_xboole_0
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(X3,X4) = X5
    | k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) != k2_zfmisc_1(X5,X6) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_33,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,X21) != k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | k4_xboole_0(X20,X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_34,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_35,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = X1
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_40,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X4,X1) != k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( X1 = k3_xboole_0(esk4_0,esk6_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_48]),c_0_43])]),c_0_49])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(X3,X4) = X5
    | k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) != k2_zfmisc_1(X6,X5) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_50]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk6_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk6_0) = X1
    | k2_zfmisc_1(esk3_0,k1_xboole_0) != k2_zfmisc_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41]),c_0_45]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:25:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.12/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.37  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.12/0.37  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.12/0.37  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.12/0.37  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.12/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.12/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.37  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.12/0.37  fof(c_0_10, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X11, X12]:((~r1_xboole_0(X11,X12)|k3_xboole_0(X11,X12)=k1_xboole_0)&(k3_xboole_0(X11,X12)!=k1_xboole_0|r1_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.12/0.37  fof(c_0_13, plain, ![X31, X32, X33, X34]:((~r1_xboole_0(X31,X32)|r1_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X34)))&(~r1_xboole_0(X33,X34)|r1_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.12/0.37  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_17, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_18, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_19, plain, ![X35, X36, X37, X38]:((X35=X37|(X35=k1_xboole_0|X36=k1_xboole_0)|k2_zfmisc_1(X35,X36)!=k2_zfmisc_1(X37,X38))&(X36=X38|(X35=k1_xboole_0|X36=k1_xboole_0)|k2_zfmisc_1(X35,X36)!=k2_zfmisc_1(X37,X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_20, plain, ![X27, X28, X29, X30]:k2_zfmisc_1(k3_xboole_0(X27,X28),k3_xboole_0(X29,X30))=k3_xboole_0(k2_zfmisc_1(X27,X29),k2_zfmisc_1(X28,X30)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  cnf(c_0_22, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k1_xboole_0|~r1_xboole_0(X2,X4)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_24, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k1_xboole_0|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_18])).
% 0.12/0.37  cnf(c_0_25, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_26, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (~r1_xboole_0(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.12/0.37  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (~r1_xboole_0(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_24]), c_0_23])).
% 0.12/0.37  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(X3,X4)=X5|k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))!=k2_zfmisc_1(X5,X6)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.12/0.37  fof(c_0_33, plain, ![X20, X21]:((k4_xboole_0(X20,X21)!=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|k4_xboole_0(X20,X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.12/0.37  fof(c_0_34, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.37  cnf(c_0_35, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=X1|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(X1,X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_21]), c_0_31]), c_0_32])).
% 0.12/0.37  cnf(c_0_37, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.37  fof(c_0_39, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.37  cnf(c_0_40, plain, (X1=k3_xboole_0(X2,X3)|X4=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X4,X1)!=k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3))), inference(spm,[status(thm)],[c_0_35, c_0_26])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk3_0), inference(er,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_42, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_43, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (X1=k3_xboole_0(esk4_0,esk6_0)|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_21])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_41])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_43])])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=esk4_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_44]), c_0_45])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (~r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_48]), c_0_43])]), c_0_49])).
% 0.12/0.37  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(X3,X4)=X5|k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))!=k2_zfmisc_1(X6,X5)), inference(spm,[status(thm)],[c_0_35, c_0_26])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_50]), c_0_50])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk6_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_50])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk6_0)=X1|k2_zfmisc_1(esk3_0,k1_xboole_0)!=k2_zfmisc_1(X2,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41]), c_0_45]), c_0_53])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_53]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 56
% 0.12/0.37  # Proof object clause steps            : 37
% 0.12/0.37  # Proof object formula steps           : 19
% 0.12/0.37  # Proof object conjectures             : 23
% 0.12/0.37  # Proof object clause conjectures      : 20
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 18
% 0.12/0.37  # Proof object simplifying inferences  : 21
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 13
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 21
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 20
% 0.12/0.37  # Processed clauses                    : 133
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 56
% 0.12/0.37  # ...remaining for further processing  : 77
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 14
% 0.12/0.37  # Generated clauses                    : 330
% 0.12/0.37  # ...of the previous two non-trivial   : 308
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 322
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 8
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 62
% 0.12/0.37  #    Positive orientable unit clauses  : 7
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 8
% 0.12/0.37  #    Non-unit-clauses                  : 46
% 0.12/0.37  # Current number of unprocessed clauses: 187
% 0.12/0.37  # ...number of literals in the above   : 474
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 16
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 240
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 182
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 37
% 0.12/0.37  # Unit Clause-clause subsumption calls : 97
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 5
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4458
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
