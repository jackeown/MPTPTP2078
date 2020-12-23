%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:30 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 102 expanded)
%              Number of clauses        :   28 (  43 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 377 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t143_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t33_finset_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(t32_finset_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & v1_finset_1(X5)
              & r1_tarski(X5,X3)
              & r1_tarski(X1,k2_zfmisc_1(X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ~ r1_tarski(X18,k2_zfmisc_1(X20,X21))
      | ~ r1_tarski(X19,k2_zfmisc_1(X22,X23))
      | r1_tarski(k2_xboole_0(X18,X19),k2_zfmisc_1(k2_xboole_0(X20,X22),k2_xboole_0(X21,X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_zfmisc_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( v1_finset_1(X1)
          & r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & ! [X4] :
              ~ ( v1_finset_1(X4)
                & r1_tarski(X4,X2)
                & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_finset_1])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_xboole_0(X1,X4),k2_zfmisc_1(k2_xboole_0(X2,X5),k2_xboole_0(X3,X6)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X4,k2_zfmisc_1(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_13,plain,(
    ! [X24,X25,X26] :
      ( ( v1_finset_1(esk2_3(X24,X25,X26))
        | ~ v1_finset_1(X24)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26)) )
      & ( r1_tarski(esk2_3(X24,X25,X26),X25)
        | ~ v1_finset_1(X24)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26)) )
      & ( v1_finset_1(esk3_3(X24,X25,X26))
        | ~ v1_finset_1(X24)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26)) )
      & ( r1_tarski(esk3_3(X24,X25,X26),X26)
        | ~ v1_finset_1(X24)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26)) )
      & ( r1_tarski(X24,k2_zfmisc_1(esk2_3(X24,X25,X26),esk3_3(X24,X25,X26)))
        | ~ v1_finset_1(X24)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X32] :
      ( v1_finset_1(esk4_0)
      & r1_tarski(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))
      & ( ~ v1_finset_1(X32)
        | ~ r1_tarski(X32,esk5_0)
        | ~ r1_tarski(esk4_0,k2_zfmisc_1(X32,esk6_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(k2_xboole_0(X13,X14),X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_xboole_0(X1,k2_zfmisc_1(X2,X3)),k2_zfmisc_1(k2_xboole_0(X4,X2),k2_xboole_0(X5,X3)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_finset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(esk3_3(X1,X2,X3),X3)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_3(esk4_0,esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20])])).

cnf(c_0_29,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X2)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( v1_finset_1(esk2_3(X1,X2,X3))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0))) = k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(esk3_3(esk4_0,esk5_0,esk6_0),esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk5_0)
    | ~ r1_tarski(esk4_0,k2_zfmisc_1(X1,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk2_3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_19]),c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( v1_finset_1(esk2_3(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk3_3(esk4_0,esk5_0,esk6_0)),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.58  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.39/0.58  # and selection function SelectNewComplexAHP.
% 0.39/0.58  #
% 0.39/0.58  # Preprocessing time       : 0.042 s
% 0.39/0.58  
% 0.39/0.58  # Proof found!
% 0.39/0.58  # SZS status Theorem
% 0.39/0.58  # SZS output start CNFRefutation
% 0.39/0.58  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.39/0.58  fof(t143_zfmisc_1, axiom, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.39/0.58  fof(t33_finset_1, conjecture, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_finset_1)).
% 0.39/0.58  fof(t32_finset_1, axiom, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4, X5]:~(((((v1_finset_1(X4)&r1_tarski(X4,X2))&v1_finset_1(X5))&r1_tarski(X5,X3))&r1_tarski(X1,k2_zfmisc_1(X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_finset_1)).
% 0.39/0.58  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.39/0.58  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.39/0.58  fof(c_0_6, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.39/0.58  fof(c_0_7, plain, ![X18, X19, X20, X21, X22, X23]:(~r1_tarski(X18,k2_zfmisc_1(X20,X21))|~r1_tarski(X19,k2_zfmisc_1(X22,X23))|r1_tarski(k2_xboole_0(X18,X19),k2_zfmisc_1(k2_xboole_0(X20,X22),k2_xboole_0(X21,X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_zfmisc_1])])).
% 0.39/0.58  cnf(c_0_8, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.39/0.58  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.39/0.58  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3))))))), inference(assume_negation,[status(cth)],[t33_finset_1])).
% 0.39/0.58  cnf(c_0_11, plain, (r1_tarski(k2_xboole_0(X1,X4),k2_zfmisc_1(k2_xboole_0(X2,X5),k2_xboole_0(X3,X6)))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X4,k2_zfmisc_1(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.39/0.58  cnf(c_0_12, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.39/0.58  fof(c_0_13, plain, ![X24, X25, X26]:(((((v1_finset_1(esk2_3(X24,X25,X26))|(~v1_finset_1(X24)|~r1_tarski(X24,k2_zfmisc_1(X25,X26))))&(r1_tarski(esk2_3(X24,X25,X26),X25)|(~v1_finset_1(X24)|~r1_tarski(X24,k2_zfmisc_1(X25,X26)))))&(v1_finset_1(esk3_3(X24,X25,X26))|(~v1_finset_1(X24)|~r1_tarski(X24,k2_zfmisc_1(X25,X26)))))&(r1_tarski(esk3_3(X24,X25,X26),X26)|(~v1_finset_1(X24)|~r1_tarski(X24,k2_zfmisc_1(X25,X26)))))&(r1_tarski(X24,k2_zfmisc_1(esk2_3(X24,X25,X26),esk3_3(X24,X25,X26)))|(~v1_finset_1(X24)|~r1_tarski(X24,k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).
% 0.39/0.58  fof(c_0_14, negated_conjecture, ![X32]:((v1_finset_1(esk4_0)&r1_tarski(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)))&(~v1_finset_1(X32)|~r1_tarski(X32,esk5_0)|~r1_tarski(esk4_0,k2_zfmisc_1(X32,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.39/0.58  fof(c_0_15, plain, ![X13, X14, X15]:(~r1_tarski(k2_xboole_0(X13,X14),X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.39/0.58  cnf(c_0_16, plain, (r1_tarski(k2_xboole_0(X1,k2_zfmisc_1(X2,X3)),k2_zfmisc_1(k2_xboole_0(X4,X2),k2_xboole_0(X5,X3)))|~r1_tarski(X1,k2_zfmisc_1(X4,X5))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.39/0.58  fof(c_0_17, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.39/0.58  cnf(c_0_18, plain, (r1_tarski(X1,k2_zfmisc_1(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.58  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.58  cnf(c_0_20, negated_conjecture, (v1_finset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.58  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.58  cnf(c_0_22, plain, (r1_tarski(k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)))), inference(spm,[status(thm)],[c_0_16, c_0_12])).
% 0.39/0.58  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.58  cnf(c_0_24, plain, (r1_tarski(esk3_3(X1,X2,X3),X3)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.58  cnf(c_0_25, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.39/0.58  cnf(c_0_26, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.39/0.58  cnf(c_0_27, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_12])).
% 0.39/0.58  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_3(esk4_0,esk5_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_20])])).
% 0.39/0.58  cnf(c_0_29, plain, (r1_tarski(esk2_3(X1,X2,X3),X2)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.58  cnf(c_0_30, plain, (v1_finset_1(esk2_3(X1,X2,X3))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.58  cnf(c_0_31, negated_conjecture, (k2_xboole_0(esk4_0,k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0)))=k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.39/0.58  cnf(c_0_32, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.39/0.58  cnf(c_0_33, negated_conjecture, (k2_xboole_0(esk3_3(esk4_0,esk5_0,esk6_0),esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_23, c_0_28])).
% 0.39/0.58  cnf(c_0_34, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(X1,esk5_0)|~r1_tarski(esk4_0,k2_zfmisc_1(X1,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.58  cnf(c_0_35, negated_conjecture, (r1_tarski(esk2_3(esk4_0,esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_19]), c_0_20])])).
% 0.39/0.58  cnf(c_0_36, negated_conjecture, (v1_finset_1(esk2_3(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_20])])).
% 0.39/0.58  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk3_3(esk4_0,esk5_0,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.39/0.58  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk3_3(esk4_0,esk5_0,esk6_0)),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.39/0.58  cnf(c_0_39, negated_conjecture, (~r1_tarski(esk4_0,k2_zfmisc_1(esk2_3(esk4_0,esk5_0,esk6_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.39/0.58  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.39/0.58  # SZS output end CNFRefutation
% 0.39/0.58  # Proof object total steps             : 41
% 0.39/0.58  # Proof object clause steps            : 28
% 0.39/0.58  # Proof object formula steps           : 13
% 0.39/0.58  # Proof object conjectures             : 16
% 0.39/0.58  # Proof object clause conjectures      : 13
% 0.39/0.58  # Proof object formula conjectures     : 3
% 0.39/0.58  # Proof object initial clauses used    : 12
% 0.39/0.58  # Proof object initial formulas used   : 6
% 0.39/0.58  # Proof object generating inferences   : 16
% 0.39/0.58  # Proof object simplifying inferences  : 11
% 0.39/0.58  # Training examples: 0 positive, 0 negative
% 0.39/0.58  # Parsed axioms                        : 6
% 0.39/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.58  # Initial clauses                      : 14
% 0.39/0.58  # Removed in clause preprocessing      : 0
% 0.39/0.58  # Initial clauses in saturation        : 14
% 0.39/0.58  # Processed clauses                    : 2339
% 0.39/0.58  # ...of these trivial                  : 337
% 0.39/0.58  # ...subsumed                          : 1574
% 0.39/0.58  # ...remaining for further processing  : 428
% 0.39/0.58  # Other redundant clauses eliminated   : 0
% 0.39/0.58  # Clauses deleted for lack of memory   : 0
% 0.39/0.58  # Backward-subsumed                    : 10
% 0.39/0.58  # Backward-rewritten                   : 16
% 0.39/0.58  # Generated clauses                    : 13680
% 0.39/0.58  # ...of the previous two non-trivial   : 12091
% 0.39/0.58  # Contextual simplify-reflections      : 0
% 0.39/0.58  # Paramodulations                      : 13680
% 0.39/0.58  # Factorizations                       : 0
% 0.39/0.58  # Equation resolutions                 : 0
% 0.39/0.58  # Propositional unsat checks           : 0
% 0.39/0.58  #    Propositional check models        : 0
% 0.39/0.58  #    Propositional check unsatisfiable : 0
% 0.39/0.58  #    Propositional clauses             : 0
% 0.39/0.58  #    Propositional clauses after purity: 0
% 0.39/0.58  #    Propositional unsat core size     : 0
% 0.39/0.58  #    Propositional preprocessing time  : 0.000
% 0.39/0.58  #    Propositional encoding time       : 0.000
% 0.39/0.58  #    Propositional solver time         : 0.000
% 0.39/0.58  #    Success case prop preproc time    : 0.000
% 0.39/0.58  #    Success case prop encoding time   : 0.000
% 0.39/0.58  #    Success case prop solver time     : 0.000
% 0.39/0.58  # Current number of processed clauses  : 402
% 0.39/0.58  #    Positive orientable unit clauses  : 199
% 0.39/0.58  #    Positive unorientable unit clauses: 0
% 0.39/0.58  #    Negative unit clauses             : 18
% 0.39/0.58  #    Non-unit-clauses                  : 185
% 0.39/0.58  # Current number of unprocessed clauses: 9753
% 0.39/0.58  # ...number of literals in the above   : 13136
% 0.39/0.58  # Current number of archived formulas  : 0
% 0.39/0.58  # Current number of archived clauses   : 26
% 0.39/0.58  # Clause-clause subsumption calls (NU) : 15658
% 0.39/0.58  # Rec. Clause-clause subsumption calls : 11559
% 0.39/0.58  # Non-unit clause-clause subsumptions  : 871
% 0.39/0.58  # Unit Clause-clause subsumption calls : 888
% 0.39/0.58  # Rewrite failures with RHS unbound    : 0
% 0.39/0.58  # BW rewrite match attempts            : 395
% 0.39/0.58  # BW rewrite match successes           : 16
% 0.39/0.58  # Condensation attempts                : 0
% 0.39/0.58  # Condensation successes               : 0
% 0.39/0.58  # Termbank termtop insertions          : 199053
% 0.39/0.58  
% 0.39/0.58  # -------------------------------------------------
% 0.39/0.58  # User time                : 0.202 s
% 0.39/0.58  # System time              : 0.012 s
% 0.39/0.58  # Total time               : 0.214 s
% 0.39/0.58  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
