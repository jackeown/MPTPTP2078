%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:13 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 130 expanded)
%              Number of clauses        :   34 (  56 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 396 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t30_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_11,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(k3_tarski(X11),X12)
      | ~ r2_hidden(X13,X11)
      | r1_tarski(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(k3_tarski(X9),k3_tarski(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_ordinal1(X16)
        | ~ r2_hidden(X17,X16)
        | r1_tarski(X17,X16) )
      & ( r2_hidden(esk2_1(X18),X18)
        | v1_ordinal1(X18) )
      & ( ~ r1_tarski(esk2_1(X18),X18)
        | v1_ordinal1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_tarski(k3_tarski(X6),X7) )
      & ( ~ r1_tarski(esk1_2(X6,X7),X7)
        | r1_tarski(k3_tarski(X6),X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t30_ordinal1])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X14,X15] :
      ( ~ v3_ordinal1(X14)
      | ~ v3_ordinal1(X15)
      | r1_ordinal1(X14,X15)
      | r1_ordinal1(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_23,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & ~ v3_ordinal1(k3_tarski(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X25)
      | ~ r2_hidden(X24,X25)
      | v3_ordinal1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_25,plain,(
    ! [X22,X23] :
      ( ~ v1_ordinal1(X22)
      | ~ v3_ordinal1(X23)
      | ~ r2_xboole_0(X22,X23)
      | r2_hidden(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

fof(c_0_26,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | ~ r2_xboole_0(X4,X5) )
      & ( X4 != X5
        | ~ r2_xboole_0(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | X4 = X5
        | r2_xboole_0(X4,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_27,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( v1_ordinal1(X1)
    | r1_tarski(esk2_1(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( r1_tarski(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r1_tarski(k3_tarski(X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_tarski(X1),X1)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    ! [X20,X21] :
      ( ( ~ r1_ordinal1(X20,X21)
        | r1_tarski(X20,X21)
        | ~ v3_ordinal1(X20)
        | ~ v3_ordinal1(X21) )
      & ( ~ r1_tarski(X20,X21)
        | r1_ordinal1(X20,X21)
        | ~ v3_ordinal1(X20)
        | ~ v3_ordinal1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_39,negated_conjecture,
    ( r1_ordinal1(esk3_0,X1)
    | r1_ordinal1(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( v1_ordinal1(X1)
    | v3_ordinal1(esk2_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

cnf(c_0_41,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v1_ordinal1(X1)
    | r1_ordinal1(esk2_1(X1),esk3_0)
    | r1_ordinal1(esk3_0,esk2_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_45,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | ~ r1_tarski(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_46,plain,
    ( k3_tarski(X1) = X2
    | r2_hidden(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_ordinal1(X1)
    | r1_ordinal1(esk3_0,esk2_1(X1))
    | r1_tarski(esk2_1(X1),esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32])]),c_0_40])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( k3_tarski(X1) = X2
    | v3_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( v1_ordinal1(X1)
    | r1_tarski(esk2_1(X1),esk3_0)
    | r1_tarski(esk3_0,esk2_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_47]),c_0_32])]),c_0_40])).

cnf(c_0_51,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(X1,esk2_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,plain,
    ( k3_tarski(X1) = X1
    | v3_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( v1_ordinal1(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_50]),c_0_32])]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k3_tarski(esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_32])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_55]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:26:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.029 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.12/0.37  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.12/0.37  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.12/0.37  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.12/0.37  fof(t30_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 0.12/0.37  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.12/0.37  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.12/0.37  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.12/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.12/0.37  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(c_0_11, plain, ![X11, X12, X13]:(~r1_tarski(k3_tarski(X11),X12)|~r2_hidden(X13,X11)|r1_tarski(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.12/0.37  fof(c_0_12, plain, ![X9, X10]:(~r1_tarski(X9,X10)|r1_tarski(k3_tarski(X9),k3_tarski(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_13, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_14, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_15, plain, ![X16, X17, X18]:((~v1_ordinal1(X16)|(~r2_hidden(X17,X16)|r1_tarski(X17,X16)))&((r2_hidden(esk2_1(X18),X18)|v1_ordinal1(X18))&(~r1_tarski(esk2_1(X18),X18)|v1_ordinal1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.12/0.37  fof(c_0_16, plain, ![X6, X7]:((r2_hidden(esk1_2(X6,X7),X6)|r1_tarski(k3_tarski(X6),X7))&(~r1_tarski(esk1_2(X6,X7),X7)|r1_tarski(k3_tarski(X6),X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t30_ordinal1])).
% 0.12/0.37  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_19, plain, (r2_hidden(esk2_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_20, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  fof(c_0_22, plain, ![X14, X15]:(~v3_ordinal1(X14)|~v3_ordinal1(X15)|(r1_ordinal1(X14,X15)|r1_ordinal1(X15,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.12/0.37  fof(c_0_23, negated_conjecture, (v3_ordinal1(esk3_0)&~v3_ordinal1(k3_tarski(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.12/0.37  fof(c_0_24, plain, ![X24, X25]:(~v3_ordinal1(X25)|(~r2_hidden(X24,X25)|v3_ordinal1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.12/0.37  fof(c_0_25, plain, ![X22, X23]:(~v1_ordinal1(X22)|(~v3_ordinal1(X23)|(~r2_xboole_0(X22,X23)|r2_hidden(X22,X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.12/0.37  fof(c_0_26, plain, ![X4, X5]:(((r1_tarski(X4,X5)|~r2_xboole_0(X4,X5))&(X4!=X5|~r2_xboole_0(X4,X5)))&(~r1_tarski(X4,X5)|X4=X5|r2_xboole_0(X4,X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.12/0.37  cnf(c_0_27, plain, (v1_ordinal1(X1)|~r1_tarski(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_28, plain, (v1_ordinal1(X1)|r1_tarski(esk2_1(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_29, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_30, plain, (r1_tarski(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.37  cnf(c_0_31, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_33, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_35, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_36, plain, (v1_ordinal1(k3_tarski(X1))|~r1_tarski(k3_tarski(X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_37, plain, (r1_tarski(k3_tarski(X1),X1)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  fof(c_0_38, plain, ![X20, X21]:((~r1_ordinal1(X20,X21)|r1_tarski(X20,X21)|(~v3_ordinal1(X20)|~v3_ordinal1(X21)))&(~r1_tarski(X20,X21)|r1_ordinal1(X20,X21)|(~v3_ordinal1(X20)|~v3_ordinal1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (r1_ordinal1(esk3_0,X1)|r1_ordinal1(X1,esk3_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.37  cnf(c_0_40, plain, (v1_ordinal1(X1)|v3_ordinal1(esk2_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 0.12/0.37  cnf(c_0_41, plain, (X1=X2|r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_42, plain, (v1_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.37  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (v1_ordinal1(X1)|r1_ordinal1(esk2_1(X1),esk3_0)|r1_ordinal1(esk3_0,esk2_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.37  fof(c_0_45, plain, ![X26, X27]:(~r2_hidden(X26,X27)|~r1_tarski(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  cnf(c_0_46, plain, (k3_tarski(X1)=X2|r2_hidden(k3_tarski(X1),X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (v1_ordinal1(X1)|r1_ordinal1(esk3_0,esk2_1(X1))|r1_tarski(esk2_1(X1),esk3_0)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32])]), c_0_40])).
% 0.12/0.37  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.37  cnf(c_0_49, plain, (k3_tarski(X1)=X2|v3_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_46])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (v1_ordinal1(X1)|r1_tarski(esk2_1(X1),esk3_0)|r1_tarski(esk3_0,esk2_1(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_47]), c_0_32])]), c_0_40])).
% 0.12/0.37  cnf(c_0_51, plain, (v1_ordinal1(X1)|~r1_tarski(X1,esk2_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_19])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (~v3_ordinal1(k3_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_53, plain, (k3_tarski(X1)=X1|v3_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_37])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (v1_ordinal1(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_50]), c_0_32])]), c_0_51])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (k3_tarski(esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_32])])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_55]), c_0_32])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 57
% 0.12/0.37  # Proof object clause steps            : 34
% 0.12/0.37  # Proof object formula steps           : 23
% 0.12/0.37  # Proof object conjectures             : 12
% 0.12/0.37  # Proof object clause conjectures      : 9
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 11
% 0.12/0.37  # Proof object generating inferences   : 18
% 0.12/0.37  # Proof object simplifying inferences  : 15
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 11
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 18
% 0.12/0.37  # Processed clauses                    : 83
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 4
% 0.12/0.37  # ...remaining for further processing  : 79
% 0.12/0.37  # Other redundant clauses eliminated   : 1
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 148
% 0.12/0.37  # ...of the previous two non-trivial   : 101
% 0.12/0.37  # Contextual simplify-reflections      : 3
% 0.12/0.37  # Paramodulations                      : 147
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
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
% 0.12/0.37  # Current number of processed clauses  : 77
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 71
% 0.12/0.37  # Current number of unprocessed clauses: 36
% 0.12/0.37  # ...number of literals in the above   : 205
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 1
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 552
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 308
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.12/0.38  # Unit Clause-clause subsumption calls : 90
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4517
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.038 s
% 0.12/0.38  # System time              : 0.000 s
% 0.12/0.38  # Total time               : 0.038 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
