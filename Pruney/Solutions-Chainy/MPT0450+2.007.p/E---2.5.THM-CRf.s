%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:31 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 481 expanded)
%              Number of clauses        :   34 ( 242 expanded)
%              Number of leaves         :   11 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 (1092 expanded)
%              Number of equality atoms :   13 ( 232 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,X35)
      | r1_xboole_0(X34,k4_xboole_0(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_15,plain,(
    ! [X17,X18] : r1_tarski(k3_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_16,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,k2_xboole_0(X32,X33))
      | ~ r1_xboole_0(X31,X33)
      | r1_tarski(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k2_xboole_0(X14,X15),X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] : r1_tarski(k2_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X25)),k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X19,X21)
      | r1_tarski(X19,k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

fof(c_0_34,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X61)
      | ~ v1_relat_1(X62)
      | ~ r1_tarski(X61,X62)
      | r1_tarski(k3_relat_1(X61),k3_relat_1(X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_35,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X55)
      | v1_relat_1(k3_xboole_0(X55,X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_20]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,X1)),k3_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_48]),c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k3_relat_1(esk3_0)))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(X1,esk2_0)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk2_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_51]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.74/0.97  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S064A
% 0.74/0.97  # and selection function SelectComplexG.
% 0.74/0.97  #
% 0.74/0.97  # Preprocessing time       : 0.028 s
% 0.74/0.97  # Presaturation interreduction done
% 0.74/0.97  
% 0.74/0.97  # Proof found!
% 0.74/0.97  # SZS status Theorem
% 0.74/0.97  # SZS output start CNFRefutation
% 0.74/0.97  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.74/0.97  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.74/0.97  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.74/0.97  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.74/0.97  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.74/0.97  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.74/0.97  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.74/0.97  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.74/0.97  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.74/0.97  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.74/0.97  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 0.74/0.97  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.74/0.97  fof(c_0_12, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|r1_xboole_0(X34,k4_xboole_0(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.74/0.97  cnf(c_0_13, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.74/0.97  fof(c_0_14, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.74/0.97  fof(c_0_15, plain, ![X17, X18]:r1_tarski(k3_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.74/0.97  fof(c_0_16, plain, ![X31, X32, X33]:(~r1_tarski(X31,k2_xboole_0(X32,X33))|~r1_xboole_0(X31,X33)|r1_tarski(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.74/0.97  cnf(c_0_17, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.74/0.97  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_13])).
% 0.74/0.97  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.97  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.74/0.97  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.74/0.97  cnf(c_0_22, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.74/0.97  cnf(c_0_23, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.74/0.97  fof(c_0_24, plain, ![X14, X15, X16]:(~r1_tarski(k2_xboole_0(X14,X15),X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.74/0.97  fof(c_0_25, plain, ![X23, X24, X25]:r1_tarski(k2_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X25)),k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.74/0.97  cnf(c_0_26, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.74/0.97  cnf(c_0_27, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.74/0.97  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.74/0.97  fof(c_0_29, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X19,X21)|r1_tarski(X19,k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.74/0.97  cnf(c_0_30, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.74/0.97  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.74/0.97  cnf(c_0_32, plain, (r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.74/0.97  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.74/0.97  fof(c_0_34, plain, ![X61, X62]:(~v1_relat_1(X61)|(~v1_relat_1(X62)|(~r1_tarski(X61,X62)|r1_tarski(k3_relat_1(X61),k3_relat_1(X62))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.74/0.97  fof(c_0_35, plain, ![X55, X56]:(~v1_relat_1(X55)|v1_relat_1(k3_xboole_0(X55,X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.74/0.97  fof(c_0_36, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.74/0.97  cnf(c_0_37, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.74/0.97  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.74/0.97  cnf(c_0_39, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.74/0.97  cnf(c_0_40, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.74/0.97  cnf(c_0_41, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.74/0.97  fof(c_0_42, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.74/0.97  cnf(c_0_43, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_37, c_0_20])).
% 0.74/0.97  cnf(c_0_44, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.74/0.97  cnf(c_0_45, plain, (r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_20]), c_0_41])).
% 0.74/0.97  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.74/0.97  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.74/0.97  cnf(c_0_48, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.74/0.97  cnf(c_0_49, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,X1)),k3_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.74/0.97  cnf(c_0_50, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.74/0.97  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_48]), c_0_48])])).
% 0.74/0.97  cnf(c_0_52, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.74/0.97  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k3_relat_1(esk3_0)))|~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_37, c_0_49])).
% 0.74/0.97  cnf(c_0_54, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(X1,esk2_0)),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.74/0.97  cnf(c_0_55, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk2_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_51]), c_0_51])).
% 0.74/0.97  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_51]), c_0_55]), ['proof']).
% 0.74/0.97  # SZS output end CNFRefutation
% 0.74/0.97  # Proof object total steps             : 57
% 0.74/0.97  # Proof object clause steps            : 34
% 0.74/0.97  # Proof object formula steps           : 23
% 0.74/0.97  # Proof object conjectures             : 12
% 0.74/0.97  # Proof object clause conjectures      : 9
% 0.74/0.97  # Proof object formula conjectures     : 3
% 0.74/0.97  # Proof object initial clauses used    : 14
% 0.74/0.97  # Proof object initial formulas used   : 11
% 0.74/0.97  # Proof object generating inferences   : 18
% 0.74/0.97  # Proof object simplifying inferences  : 10
% 0.74/0.97  # Training examples: 0 positive, 0 negative
% 0.74/0.97  # Parsed axioms                        : 26
% 0.74/0.97  # Removed by relevancy pruning/SinE    : 0
% 0.74/0.97  # Initial clauses                      : 38
% 0.74/0.97  # Removed in clause preprocessing      : 0
% 0.74/0.97  # Initial clauses in saturation        : 38
% 0.74/0.97  # Processed clauses                    : 2755
% 0.74/0.97  # ...of these trivial                  : 308
% 0.74/0.97  # ...subsumed                          : 1149
% 0.74/0.97  # ...remaining for further processing  : 1298
% 0.74/0.97  # Other redundant clauses eliminated   : 11
% 0.74/0.97  # Clauses deleted for lack of memory   : 0
% 0.74/0.97  # Backward-subsumed                    : 7
% 0.74/0.97  # Backward-rewritten                   : 353
% 0.74/0.97  # Generated clauses                    : 48641
% 0.74/0.97  # ...of the previous two non-trivial   : 43743
% 0.74/0.97  # Contextual simplify-reflections      : 10
% 0.74/0.97  # Paramodulations                      : 48630
% 0.74/0.97  # Factorizations                       : 0
% 0.74/0.97  # Equation resolutions                 : 11
% 0.74/0.97  # Propositional unsat checks           : 0
% 0.74/0.97  #    Propositional check models        : 0
% 0.74/0.97  #    Propositional check unsatisfiable : 0
% 0.74/0.97  #    Propositional clauses             : 0
% 0.74/0.97  #    Propositional clauses after purity: 0
% 0.74/0.97  #    Propositional unsat core size     : 0
% 0.74/0.97  #    Propositional preprocessing time  : 0.000
% 0.74/0.97  #    Propositional encoding time       : 0.000
% 0.74/0.97  #    Propositional solver time         : 0.000
% 0.74/0.97  #    Success case prop preproc time    : 0.000
% 0.74/0.97  #    Success case prop encoding time   : 0.000
% 0.74/0.97  #    Success case prop solver time     : 0.000
% 0.74/0.97  # Current number of processed clauses  : 898
% 0.74/0.97  #    Positive orientable unit clauses  : 414
% 0.74/0.97  #    Positive unorientable unit clauses: 1
% 0.74/0.97  #    Negative unit clauses             : 1
% 0.74/0.97  #    Non-unit-clauses                  : 482
% 0.74/0.97  # Current number of unprocessed clauses: 40793
% 0.74/0.97  # ...number of literals in the above   : 178892
% 0.74/0.97  # Current number of archived formulas  : 0
% 0.74/0.97  # Current number of archived clauses   : 395
% 0.74/0.97  # Clause-clause subsumption calls (NU) : 58440
% 0.74/0.97  # Rec. Clause-clause subsumption calls : 11930
% 0.74/0.97  # Non-unit clause-clause subsumptions  : 1164
% 0.74/0.97  # Unit Clause-clause subsumption calls : 6457
% 0.74/0.97  # Rewrite failures with RHS unbound    : 0
% 0.74/0.97  # BW rewrite match attempts            : 27125
% 0.74/0.97  # BW rewrite match successes           : 582
% 0.74/0.97  # Condensation attempts                : 0
% 0.74/0.97  # Condensation successes               : 0
% 0.74/0.97  # Termbank termtop insertions          : 1086129
% 0.74/0.97  
% 0.74/0.97  # -------------------------------------------------
% 0.74/0.97  # User time                : 0.586 s
% 0.74/0.97  # System time              : 0.034 s
% 0.74/0.97  # Total time               : 0.621 s
% 0.74/0.97  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
