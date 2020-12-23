%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:16 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 602 expanded)
%              Number of clauses        :   38 ( 251 expanded)
%              Number of leaves         :   12 ( 158 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 (1439 expanded)
%              Number of equality atoms :   27 ( 308 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_13,plain,(
    ! [X14] : k1_ordinal1(X14) = k2_xboole_0(X14,k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_14,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & v3_ordinal1(esk2_0)
    & ( ~ r2_hidden(esk1_0,esk2_0)
      | ~ r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) )
    & ( r2_hidden(esk1_0,esk2_0)
      | r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X12,X13] : k3_tarski(k2_tarski(X12,X13)) = k2_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( ( ~ r1_ordinal1(X15,X16)
        | r1_tarski(X15,X16)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X16) )
      & ( ~ r1_tarski(X15,X16)
        | r1_ordinal1(X15,X16)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X21] :
      ( ~ v3_ordinal1(X21)
      | v3_ordinal1(k1_ordinal1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(k2_xboole_0(X8,X9),X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r1_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X17,X18] :
      ( ( ~ r2_hidden(X17,k1_ordinal1(X18))
        | r2_hidden(X17,X18)
        | X17 = X18 )
      & ( ~ r2_hidden(X17,X18)
        | r2_hidden(X17,k1_ordinal1(X18)) )
      & ( X17 != X18
        | r2_hidden(X17,k1_ordinal1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    | ~ r1_ordinal1(k1_ordinal1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( ~ v3_ordinal1(X19)
      | ~ v3_ordinal1(X20)
      | r1_ordinal1(X19,X20)
      | r2_hidden(X20,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0)
    | r2_hidden(esk1_0,esk2_0)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_34,plain,
    ( v3_ordinal1(k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_21]),c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    | ~ r1_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21]),c_0_22])).

cnf(c_0_38,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_43,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ r1_tarski(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_44,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_tarski(k2_tarski(X2,k2_tarski(X2,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_21]),c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))
    | ~ v3_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_27])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ v3_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r1_tarski(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_34]),c_0_35])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,k2_tarski(X2,X2))))
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_21]),c_0_22])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_35]),c_0_27])]),c_0_55])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_60])]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.13/0.37  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.13/0.37  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.37  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.13/0.37  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.13/0.37  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.13/0.37  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.13/0.37  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.13/0.37  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.13/0.37  fof(c_0_13, plain, ![X14]:k1_ordinal1(X14)=k2_xboole_0(X14,k1_tarski(X14)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.37  fof(c_0_14, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_15, negated_conjecture, (v3_ordinal1(esk1_0)&(v3_ordinal1(esk2_0)&((~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k1_ordinal1(esk1_0),esk2_0))&(r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k1_ordinal1(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.37  cnf(c_0_16, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_18, plain, ![X12, X13]:k3_tarski(k2_tarski(X12,X13))=k2_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.37  fof(c_0_19, plain, ![X15, X16]:((~r1_ordinal1(X15,X16)|r1_tarski(X15,X16)|(~v3_ordinal1(X15)|~v3_ordinal1(X16)))&(~r1_tarski(X15,X16)|r1_ordinal1(X15,X16)|(~v3_ordinal1(X15)|~v3_ordinal1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k1_ordinal1(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_21, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_23, plain, ![X21]:(~v3_ordinal1(X21)|v3_ordinal1(k1_ordinal1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.13/0.37  fof(c_0_24, plain, ![X8, X9, X10]:(~r1_tarski(k2_xboole_0(X8,X9),X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.13/0.37  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|r1_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_28, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  fof(c_0_29, plain, ![X17, X18]:((~r2_hidden(X17,k1_ordinal1(X18))|(r2_hidden(X17,X18)|X17=X18))&((~r2_hidden(X17,X18)|r2_hidden(X17,k1_ordinal1(X18)))&(X17!=X18|r2_hidden(X17,k1_ordinal1(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k1_ordinal1(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_31, plain, ![X19, X20]:(~v3_ordinal1(X19)|(~v3_ordinal1(X20)|(r1_ordinal1(X19,X20)|r2_hidden(X20,X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.13/0.37  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0)|r2_hidden(esk1_0,esk2_0)|~v3_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.37  cnf(c_0_34, plain, (v3_ordinal1(k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_21]), c_0_22])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (v3_ordinal1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_36, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)|~r1_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_21]), c_0_22])).
% 0.13/0.37  cnf(c_0_38, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  fof(c_0_39, plain, ![X4, X5]:(~r2_hidden(X4,X5)|~r2_hidden(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.13/0.37  fof(c_0_40, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_32, c_0_22])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))),esk2_0)|r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.13/0.37  fof(c_0_43, plain, ![X22, X23]:(~r2_hidden(X22,X23)|~r1_tarski(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.37  cnf(c_0_44, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k3_tarski(k2_tarski(X2,k2_tarski(X2,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_21]), c_0_22])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_0,k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))|~v3_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))|~r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_27])])).
% 0.13/0.37  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_47, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (r1_tarski(esk1_0,esk2_0)|r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.37  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (esk1_0=esk2_0|~v3_ordinal1(k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))|~r2_hidden(esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.13/0.37  cnf(c_0_51, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (esk1_0=esk2_0|~r1_tarski(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.13/0.37  cnf(c_0_54, plain, (r1_tarski(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_38])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (esk1_0=esk2_0|~r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_34]), c_0_35])])).
% 0.13/0.37  cnf(c_0_56, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,k2_tarski(X2,X2))))|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_21]), c_0_22])).
% 0.13/0.37  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_0,esk2_0)|~r2_hidden(esk2_0,k3_tarski(k2_tarski(esk1_0,k2_tarski(esk1_0,esk1_0))))), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, (esk1_0=esk2_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_35]), c_0_27])]), c_0_55])).
% 0.13/0.37  cnf(c_0_60, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))), inference(er,[status(thm)],[c_0_56])).
% 0.13/0.37  cnf(c_0_61, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_49, c_0_57])).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_60])]), c_0_61]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 63
% 0.13/0.37  # Proof object clause steps            : 38
% 0.13/0.37  # Proof object formula steps           : 25
% 0.13/0.37  # Proof object conjectures             : 19
% 0.13/0.37  # Proof object clause conjectures      : 16
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 12
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 35
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 12
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 20
% 0.13/0.37  # Removed in clause preprocessing      : 3
% 0.13/0.37  # Initial clauses in saturation        : 17
% 0.13/0.37  # Processed clauses                    : 60
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 2
% 0.13/0.37  # ...remaining for further processing  : 57
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 2
% 0.13/0.37  # Backward-rewritten                   : 11
% 0.13/0.37  # Generated clauses                    : 46
% 0.13/0.37  # ...of the previous two non-trivial   : 42
% 0.13/0.37  # Contextual simplify-reflections      : 4
% 0.13/0.37  # Paramodulations                      : 43
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 3
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 25
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 6
% 0.13/0.37  #    Non-unit-clauses                  : 13
% 0.13/0.37  # Current number of unprocessed clauses: 14
% 0.13/0.37  # ...number of literals in the above   : 34
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 32
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 58
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 44
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.37  # Unit Clause-clause subsumption calls : 28
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 6
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1871
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.007 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
