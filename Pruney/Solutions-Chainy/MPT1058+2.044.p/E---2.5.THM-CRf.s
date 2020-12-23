%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:32 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 180 expanded)
%              Number of clauses        :   34 (  79 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 387 expanded)
%              Number of equality atoms :   41 ( 144 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_14,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(k1_relat_1(X23),X22)
      | k7_relat_1(X23,X22) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X19] :
      ( k1_relat_1(k6_relat_1(X19)) = X19
      & k2_relat_1(k6_relat_1(X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_20,plain,(
    ! [X24] :
      ( v1_relat_1(k6_relat_1(X24))
      & v1_funct_1(k6_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

fof(c_0_26,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_27,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(X28,k1_relat_1(X29))
      | r1_tarski(X28,k10_relat_1(X29,k9_relat_1(X29,X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_29,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | r1_tarski(k10_relat_1(X18,X17),k1_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_33,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_35,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | k10_relat_1(k7_relat_1(X27,X25),X26) = k3_xboole_0(X25,k10_relat_1(X27,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_24])])).

cnf(c_0_40,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(k1_relat_1(k7_relat_1(X21,X20)),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_44,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24]),c_0_23]),c_0_18])])).

cnf(c_0_48,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_24])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k7_relat_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_52,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24])])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0)),esk2_0) = k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_54]),c_0_55])).

cnf(c_0_58,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(X1,X2)),X3),k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k6_relat_1(k10_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_24])])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53]),c_0_60])]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.61/0.77  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.61/0.77  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.61/0.77  #
% 0.61/0.77  # Preprocessing time       : 0.051 s
% 0.61/0.77  # Presaturation interreduction done
% 0.61/0.77  
% 0.61/0.77  # Proof found!
% 0.61/0.77  # SZS status Theorem
% 0.61/0.77  # SZS output start CNFRefutation
% 0.61/0.77  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.61/0.77  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.61/0.77  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.61/0.77  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.61/0.77  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.61/0.77  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.61/0.77  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.61/0.77  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.61/0.77  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.61/0.77  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.61/0.77  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.61/0.77  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.61/0.77  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.61/0.77  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.61/0.77  fof(c_0_14, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.61/0.77  fof(c_0_15, plain, ![X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(k1_relat_1(X23),X22)|k7_relat_1(X23,X22)=X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.61/0.77  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.77  cnf(c_0_17, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.77  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.61/0.77  fof(c_0_19, plain, ![X19]:(k1_relat_1(k6_relat_1(X19))=X19&k2_relat_1(k6_relat_1(X19))=X19), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.61/0.77  fof(c_0_20, plain, ![X24]:(v1_relat_1(k6_relat_1(X24))&v1_funct_1(k6_relat_1(X24))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.61/0.77  fof(c_0_21, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.61/0.77  cnf(c_0_22, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.61/0.77  cnf(c_0_23, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.77  cnf(c_0_24, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.77  fof(c_0_25, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.61/0.77  fof(c_0_26, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.61/0.77  fof(c_0_27, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.61/0.77  fof(c_0_28, plain, ![X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(X28,k1_relat_1(X29))|r1_tarski(X28,k10_relat_1(X29,k9_relat_1(X29,X28))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.61/0.77  cnf(c_0_29, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.61/0.77  cnf(c_0_30, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.61/0.77  cnf(c_0_31, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.77  fof(c_0_32, plain, ![X17, X18]:(~v1_relat_1(X18)|r1_tarski(k10_relat_1(X18,X17),k1_relat_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.61/0.77  fof(c_0_33, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.61/0.77  fof(c_0_34, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.61/0.77  fof(c_0_35, plain, ![X25, X26, X27]:(~v1_relat_1(X27)|k10_relat_1(k7_relat_1(X27,X25),X26)=k3_xboole_0(X25,k10_relat_1(X27,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.61/0.77  cnf(c_0_36, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.77  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.61/0.77  cnf(c_0_38, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.61/0.77  cnf(c_0_39, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_24])])).
% 0.61/0.77  cnf(c_0_40, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.61/0.77  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.61/0.77  cnf(c_0_42, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.77  fof(c_0_43, plain, ![X20, X21]:(~v1_relat_1(X21)|r1_tarski(k1_relat_1(k7_relat_1(X21,X20)),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.61/0.77  cnf(c_0_44, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.61/0.77  cnf(c_0_45, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.61/0.77  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.77  cnf(c_0_47, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_24]), c_0_23]), c_0_18])])).
% 0.61/0.77  cnf(c_0_48, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_24])])).
% 0.61/0.77  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.61/0.77  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.77  fof(c_0_51, plain, ![X13, X14]:(~v1_relat_1(X13)|v1_relat_1(k7_relat_1(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.61/0.77  cnf(c_0_52, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.61/0.77  cnf(c_0_53, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.61/0.77  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))),esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.61/0.77  cnf(c_0_55, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.61/0.77  cnf(c_0_56, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_24])])).
% 0.61/0.77  cnf(c_0_57, negated_conjecture, (k7_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0)),esk2_0)=k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_54]), c_0_55])).
% 0.61/0.77  cnf(c_0_58, plain, (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(X1,X2)),X3),k10_relat_1(X1,X2))=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 0.61/0.77  cnf(c_0_59, negated_conjecture, (k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k6_relat_1(k10_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_30]), c_0_24])])).
% 0.61/0.77  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.77  cnf(c_0_61, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.77  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_53]), c_0_60])]), c_0_61]), ['proof']).
% 0.61/0.77  # SZS output end CNFRefutation
% 0.61/0.77  # Proof object total steps             : 63
% 0.61/0.77  # Proof object clause steps            : 34
% 0.61/0.77  # Proof object formula steps           : 29
% 0.61/0.77  # Proof object conjectures             : 11
% 0.61/0.77  # Proof object clause conjectures      : 8
% 0.61/0.77  # Proof object formula conjectures     : 3
% 0.61/0.77  # Proof object initial clauses used    : 18
% 0.61/0.77  # Proof object initial formulas used   : 14
% 0.61/0.77  # Proof object generating inferences   : 13
% 0.61/0.77  # Proof object simplifying inferences  : 25
% 0.61/0.77  # Training examples: 0 positive, 0 negative
% 0.61/0.77  # Parsed axioms                        : 14
% 0.61/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.77  # Initial clauses                      : 21
% 0.61/0.77  # Removed in clause preprocessing      : 2
% 0.61/0.77  # Initial clauses in saturation        : 19
% 0.61/0.77  # Processed clauses                    : 3581
% 0.61/0.77  # ...of these trivial                  : 6
% 0.61/0.77  # ...subsumed                          : 2965
% 0.61/0.77  # ...remaining for further processing  : 610
% 0.61/0.77  # Other redundant clauses eliminated   : 2
% 0.61/0.77  # Clauses deleted for lack of memory   : 0
% 0.61/0.77  # Backward-subsumed                    : 10
% 0.61/0.77  # Backward-rewritten                   : 1
% 0.61/0.77  # Generated clauses                    : 25631
% 0.61/0.77  # ...of the previous two non-trivial   : 24352
% 0.61/0.77  # Contextual simplify-reflections      : 31
% 0.61/0.77  # Paramodulations                      : 25629
% 0.61/0.77  # Factorizations                       : 0
% 0.61/0.77  # Equation resolutions                 : 2
% 0.61/0.77  # Propositional unsat checks           : 0
% 0.61/0.77  #    Propositional check models        : 0
% 0.61/0.77  #    Propositional check unsatisfiable : 0
% 0.61/0.77  #    Propositional clauses             : 0
% 0.61/0.77  #    Propositional clauses after purity: 0
% 0.61/0.77  #    Propositional unsat core size     : 0
% 0.61/0.77  #    Propositional preprocessing time  : 0.000
% 0.61/0.77  #    Propositional encoding time       : 0.000
% 0.61/0.77  #    Propositional solver time         : 0.000
% 0.61/0.77  #    Success case prop preproc time    : 0.000
% 0.61/0.77  #    Success case prop encoding time   : 0.000
% 0.61/0.77  #    Success case prop solver time     : 0.000
% 0.61/0.77  # Current number of processed clauses  : 579
% 0.61/0.77  #    Positive orientable unit clauses  : 24
% 0.61/0.77  #    Positive unorientable unit clauses: 1
% 0.61/0.77  #    Negative unit clauses             : 1
% 0.61/0.77  #    Non-unit-clauses                  : 553
% 0.61/0.77  # Current number of unprocessed clauses: 20628
% 0.61/0.77  # ...number of literals in the above   : 88381
% 0.61/0.77  # Current number of archived formulas  : 0
% 0.61/0.77  # Current number of archived clauses   : 31
% 0.61/0.77  # Clause-clause subsumption calls (NU) : 82278
% 0.61/0.77  # Rec. Clause-clause subsumption calls : 44164
% 0.61/0.77  # Non-unit clause-clause subsumptions  : 3006
% 0.61/0.77  # Unit Clause-clause subsumption calls : 13
% 0.61/0.77  # Rewrite failures with RHS unbound    : 0
% 0.61/0.77  # BW rewrite match attempts            : 61
% 0.61/0.77  # BW rewrite match successes           : 2
% 0.61/0.77  # Condensation attempts                : 0
% 0.61/0.77  # Condensation successes               : 0
% 0.61/0.77  # Termbank termtop insertions          : 485998
% 0.61/0.77  
% 0.61/0.77  # -------------------------------------------------
% 0.61/0.77  # User time                : 0.402 s
% 0.61/0.77  # System time              : 0.025 s
% 0.61/0.77  # Total time               : 0.427 s
% 0.61/0.77  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
