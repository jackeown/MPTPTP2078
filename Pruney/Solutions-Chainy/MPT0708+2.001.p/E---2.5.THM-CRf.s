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
% DateTime   : Thu Dec  3 10:55:28 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 157 expanded)
%              Number of clauses        :   40 (  68 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 329 expanded)
%              Number of equality atoms :   31 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t163_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | k10_relat_1(X21,k2_xboole_0(X19,X20)) = k2_xboole_0(k10_relat_1(X21,X19),k10_relat_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_13,plain,(
    ! [X23] :
      ( v1_relat_1(k6_relat_1(X23))
      & v1_funct_1(k6_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_14,plain,(
    ! [X11,X12] : r1_tarski(X11,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_15,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k10_relat_1(X18,k2_relat_1(X18)) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_18,plain,(
    ! [X22] :
      ( k1_relat_1(k6_relat_1(X22)) = X22
      & k2_relat_1(k6_relat_1(X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3)) = k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | r1_tarski(k10_relat_1(X17,X16),k1_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_25,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(X24,k1_relat_1(X25))
      | r1_tarski(X24,k10_relat_1(X25,k9_relat_1(X25,X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_30,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(X1,k1_relat_1(X3))
            & r1_tarski(k9_relat_1(X3,X1),X2) )
         => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t163_funct_1])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_23])).

cnf(c_0_35,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(esk1_0,k1_relat_1(esk3_0))
    & r1_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0)
    & ~ r1_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_40,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | r1_tarski(k2_xboole_0(X13,X15),k2_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_41,plain,
    ( k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_23]),c_0_16])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k9_relat_1(esk3_0,esk1_0),X1),k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_38]),c_0_50])).

cnf(c_0_56,plain,
    ( k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_51]),c_0_34])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k10_relat_1(esk3_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(k9_relat_1(esk3_0,esk1_0),X1) = k2_xboole_0(esk2_0,X1)
    | ~ r1_tarski(k2_xboole_0(esk2_0,X1),k2_xboole_0(k9_relat_1(esk3_0,esk1_0),X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_54])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,k2_xboole_0(X1,k9_relat_1(esk3_0,esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_38]),c_0_38]),c_0_19])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.68/0.86  # AutoSched0-Mode selected heuristic G_E___208_C09_12_F1_SE_CS_SP_PS_S064A
% 0.68/0.86  # and selection function SelectComplexG.
% 0.68/0.86  #
% 0.68/0.86  # Preprocessing time       : 0.026 s
% 0.68/0.86  # Presaturation interreduction done
% 0.68/0.86  
% 0.68/0.86  # Proof found!
% 0.68/0.86  # SZS status Theorem
% 0.68/0.86  # SZS output start CNFRefutation
% 0.68/0.86  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 0.68/0.86  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.68/0.86  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.68/0.86  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.68/0.86  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.68/0.86  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.68/0.86  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.68/0.86  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.68/0.86  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.68/0.86  fof(t163_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.68/0.86  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.68/0.86  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 0.68/0.86  fof(c_0_12, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|k10_relat_1(X21,k2_xboole_0(X19,X20))=k2_xboole_0(k10_relat_1(X21,X19),k10_relat_1(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.68/0.86  fof(c_0_13, plain, ![X23]:(v1_relat_1(k6_relat_1(X23))&v1_funct_1(k6_relat_1(X23))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.68/0.86  fof(c_0_14, plain, ![X11, X12]:r1_tarski(X11,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.68/0.86  cnf(c_0_15, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.68/0.86  cnf(c_0_16, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.68/0.86  fof(c_0_17, plain, ![X18]:(~v1_relat_1(X18)|k10_relat_1(X18,k2_relat_1(X18))=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.68/0.86  fof(c_0_18, plain, ![X22]:(k1_relat_1(k6_relat_1(X22))=X22&k2_relat_1(k6_relat_1(X22))=X22), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.68/0.86  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.68/0.86  cnf(c_0_20, plain, (k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3))=k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.68/0.86  cnf(c_0_21, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.68/0.86  cnf(c_0_22, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.68/0.86  cnf(c_0_23, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.68/0.86  fof(c_0_24, plain, ![X16, X17]:(~v1_relat_1(X17)|r1_tarski(k10_relat_1(X17,X16),k1_relat_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.68/0.86  fof(c_0_25, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.68/0.86  cnf(c_0_26, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.68/0.86  cnf(c_0_27, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_22]), c_0_23])).
% 0.68/0.86  cnf(c_0_28, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.68/0.86  fof(c_0_29, plain, ![X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(X24,k1_relat_1(X25))|r1_tarski(X24,k10_relat_1(X25,k9_relat_1(X25,X24))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.68/0.86  fof(c_0_30, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.68/0.86  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t163_funct_1])).
% 0.68/0.86  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.68/0.86  cnf(c_0_33, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.68/0.86  cnf(c_0_34, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_23])).
% 0.68/0.86  cnf(c_0_35, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.86  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.68/0.86  fof(c_0_37, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.68/0.86  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.68/0.86  fof(c_0_39, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((r1_tarski(esk1_0,k1_relat_1(esk3_0))&r1_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.68/0.86  fof(c_0_40, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|r1_tarski(k2_xboole_0(X13,X15),k2_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 0.68/0.86  cnf(c_0_41, plain, (k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.68/0.86  cnf(c_0_42, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X1)))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_23]), c_0_16])])).
% 0.68/0.86  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.68/0.86  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.68/0.86  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_19, c_0_38])).
% 0.68/0.86  cnf(c_0_46, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.68/0.86  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.68/0.86  cnf(c_0_48, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.68/0.86  cnf(c_0_49, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.68/0.86  cnf(c_0_50, plain, (k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 0.68/0.86  cnf(c_0_51, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.68/0.86  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.68/0.86  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_47])])).
% 0.68/0.86  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_xboole_0(k9_relat_1(esk3_0,esk1_0),X1),k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.68/0.86  cnf(c_0_55, plain, (k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_27]), c_0_38]), c_0_50])).
% 0.68/0.86  cnf(c_0_56, plain, (k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_51]), c_0_34])])).
% 0.68/0.86  cnf(c_0_57, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.68/0.86  cnf(c_0_58, negated_conjecture, (k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))=k10_relat_1(esk3_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_47])).
% 0.68/0.86  cnf(c_0_59, negated_conjecture, (k2_xboole_0(k9_relat_1(esk3_0,esk1_0),X1)=k2_xboole_0(esk2_0,X1)|~r1_tarski(k2_xboole_0(esk2_0,X1),k2_xboole_0(k9_relat_1(esk3_0,esk1_0),X1))), inference(spm,[status(thm)],[c_0_32, c_0_54])).
% 0.68/0.86  cnf(c_0_60, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.68/0.86  cnf(c_0_61, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,k2_xboole_0(X1,k9_relat_1(esk3_0,esk1_0))))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.68/0.86  cnf(c_0_62, negated_conjecture, (k2_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_38]), c_0_38]), c_0_19])])).
% 0.68/0.86  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.68/0.86  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), ['proof']).
% 0.68/0.86  # SZS output end CNFRefutation
% 0.68/0.86  # Proof object total steps             : 65
% 0.68/0.86  # Proof object clause steps            : 40
% 0.68/0.86  # Proof object formula steps           : 25
% 0.68/0.86  # Proof object conjectures             : 15
% 0.68/0.86  # Proof object clause conjectures      : 12
% 0.68/0.86  # Proof object formula conjectures     : 3
% 0.68/0.86  # Proof object initial clauses used    : 17
% 0.68/0.86  # Proof object initial formulas used   : 12
% 0.68/0.86  # Proof object generating inferences   : 22
% 0.68/0.86  # Proof object simplifying inferences  : 19
% 0.68/0.86  # Training examples: 0 positive, 0 negative
% 0.68/0.86  # Parsed axioms                        : 12
% 0.68/0.86  # Removed by relevancy pruning/SinE    : 0
% 0.68/0.86  # Initial clauses                      : 20
% 0.68/0.86  # Removed in clause preprocessing      : 0
% 0.68/0.86  # Initial clauses in saturation        : 20
% 0.68/0.86  # Processed clauses                    : 3956
% 0.68/0.86  # ...of these trivial                  : 888
% 0.68/0.86  # ...subsumed                          : 1814
% 0.68/0.86  # ...remaining for further processing  : 1254
% 0.68/0.86  # Other redundant clauses eliminated   : 2
% 0.68/0.86  # Clauses deleted for lack of memory   : 0
% 0.68/0.86  # Backward-subsumed                    : 27
% 0.68/0.86  # Backward-rewritten                   : 200
% 0.68/0.86  # Generated clauses                    : 63569
% 0.68/0.86  # ...of the previous two non-trivial   : 42574
% 0.68/0.86  # Contextual simplify-reflections      : 0
% 0.68/0.86  # Paramodulations                      : 63567
% 0.68/0.86  # Factorizations                       : 0
% 0.68/0.86  # Equation resolutions                 : 2
% 0.68/0.86  # Propositional unsat checks           : 0
% 0.68/0.86  #    Propositional check models        : 0
% 0.68/0.86  #    Propositional check unsatisfiable : 0
% 0.68/0.86  #    Propositional clauses             : 0
% 0.68/0.86  #    Propositional clauses after purity: 0
% 0.68/0.86  #    Propositional unsat core size     : 0
% 0.68/0.86  #    Propositional preprocessing time  : 0.000
% 0.68/0.86  #    Propositional encoding time       : 0.000
% 0.68/0.86  #    Propositional solver time         : 0.000
% 0.68/0.86  #    Success case prop preproc time    : 0.000
% 0.68/0.86  #    Success case prop encoding time   : 0.000
% 0.68/0.86  #    Success case prop solver time     : 0.000
% 0.68/0.86  # Current number of processed clauses  : 1006
% 0.68/0.86  #    Positive orientable unit clauses  : 527
% 0.68/0.86  #    Positive unorientable unit clauses: 1
% 0.68/0.86  #    Negative unit clauses             : 1
% 0.68/0.86  #    Non-unit-clauses                  : 477
% 0.68/0.86  # Current number of unprocessed clauses: 38477
% 0.68/0.86  # ...number of literals in the above   : 40464
% 0.68/0.86  # Current number of archived formulas  : 0
% 0.68/0.86  # Current number of archived clauses   : 246
% 0.68/0.86  # Clause-clause subsumption calls (NU) : 53207
% 0.68/0.86  # Rec. Clause-clause subsumption calls : 48841
% 0.68/0.86  # Non-unit clause-clause subsumptions  : 1826
% 0.68/0.86  # Unit Clause-clause subsumption calls : 983
% 0.68/0.86  # Rewrite failures with RHS unbound    : 0
% 0.68/0.86  # BW rewrite match attempts            : 5011
% 0.68/0.86  # BW rewrite match successes           : 62
% 0.68/0.86  # Condensation attempts                : 0
% 0.68/0.86  # Condensation successes               : 0
% 0.68/0.86  # Termbank termtop insertions          : 970304
% 0.68/0.86  
% 0.68/0.86  # -------------------------------------------------
% 0.68/0.86  # User time                : 0.496 s
% 0.68/0.86  # System time              : 0.026 s
% 0.68/0.86  # Total time               : 0.522 s
% 0.68/0.86  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
