%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:28 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 124 expanded)
%              Number of clauses        :   30 (  52 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 397 expanded)
%              Number of equality atoms :   23 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ( r1_tarski(X13,esk1_3(X13,X14,X15))
        | ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X15,X14)
        | X14 = k2_xboole_0(X13,X15) )
      & ( r1_tarski(X15,esk1_3(X13,X14,X15))
        | ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X15,X14)
        | X14 = k2_xboole_0(X13,X15) )
      & ( ~ r1_tarski(X14,esk1_3(X13,X14,X15))
        | ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X15,X14)
        | X14 = k2_xboole_0(X13,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,esk3_0)
    & ~ r1_tarski(k3_relat_1(esk2_0),k3_relat_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X21,X20)
      | r1_tarski(k2_xboole_0(X19,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_15,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k3_relat_1(X22) = k2_xboole_0(k1_relat_1(X22),k2_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(X7,k2_xboole_0(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_22,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_23,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k2_relat_1(k2_xboole_0(X25,X26)) = k2_xboole_0(k2_relat_1(X25),k2_relat_1(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(esk2_0,X1) = esk3_0
    | r1_tarski(X1,esk1_3(esk2_0,esk3_0,X1))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk2_0),k3_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0
    | r1_tarski(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_34,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_35,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | k1_relat_1(k2_xboole_0(X23,X24)) = k2_xboole_0(k1_relat_1(X23),k1_relat_1(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk2_0),k3_relat_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk2_0),k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(k2_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_17])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk2_0),k3_relat_1(esk3_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_38]),c_0_28])])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k2_xboole_0(X1,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk2_0),k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),X1)
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_38]),c_0_28])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk3_0),k3_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:47:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.027 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.12/0.40  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.12/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.40  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.12/0.40  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.12/0.40  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.12/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.40  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 0.12/0.40  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.12/0.40  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 0.12/0.40  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.12/0.40  fof(c_0_11, plain, ![X13, X14, X15]:(((r1_tarski(X13,esk1_3(X13,X14,X15))|(~r1_tarski(X13,X14)|~r1_tarski(X15,X14))|X14=k2_xboole_0(X13,X15))&(r1_tarski(X15,esk1_3(X13,X14,X15))|(~r1_tarski(X13,X14)|~r1_tarski(X15,X14))|X14=k2_xboole_0(X13,X15)))&(~r1_tarski(X14,esk1_3(X13,X14,X15))|(~r1_tarski(X13,X14)|~r1_tarski(X15,X14))|X14=k2_xboole_0(X13,X15))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.12/0.40  fof(c_0_12, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(r1_tarski(esk2_0,esk3_0)&~r1_tarski(k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.40  fof(c_0_13, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.40  fof(c_0_14, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X21,X20)|r1_tarski(k2_xboole_0(X19,X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.12/0.40  fof(c_0_15, plain, ![X22]:(~v1_relat_1(X22)|k3_relat_1(X22)=k2_xboole_0(k1_relat_1(X22),k2_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.12/0.40  cnf(c_0_16, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.40  cnf(c_0_17, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.40  cnf(c_0_19, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  cnf(c_0_20, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  fof(c_0_21, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(X7,k2_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.12/0.40  fof(c_0_22, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.40  fof(c_0_23, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|k2_relat_1(k2_xboole_0(X25,X26))=k2_xboole_0(k2_relat_1(X25),k2_relat_1(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 0.12/0.40  cnf(c_0_24, negated_conjecture, (k2_xboole_0(esk2_0,X1)=esk3_0|r1_tarski(X1,esk1_3(esk2_0,esk3_0,X1))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.12/0.40  cnf(c_0_26, negated_conjecture, (~r1_tarski(k3_relat_1(esk2_0),k3_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  cnf(c_0_27, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.40  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.40  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.40  cnf(c_0_31, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.40  cnf(c_0_32, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.40  cnf(c_0_33, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0|r1_tarski(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.40  fof(c_0_34, plain, ![X10, X11, X12]:(~r1_tarski(k2_xboole_0(X10,X11),X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.12/0.40  fof(c_0_35, plain, ![X23, X24]:(~v1_relat_1(X23)|(~v1_relat_1(X24)|k1_relat_1(k2_xboole_0(X23,X24))=k2_xboole_0(k1_relat_1(X23),k1_relat_1(X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 0.12/0.40  cnf(c_0_36, negated_conjecture, (~r1_tarski(k2_relat_1(esk2_0),k3_relat_1(esk3_0))|~r1_tarski(k1_relat_1(esk2_0),k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.12/0.40  cnf(c_0_37, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.12/0.40  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(k2_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.40  cnf(c_0_40, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_17])])).
% 0.12/0.40  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.40  cnf(c_0_42, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.40  cnf(c_0_43, negated_conjecture, (~r1_tarski(k1_relat_1(esk2_0),k3_relat_1(esk3_0))|~r1_tarski(k2_relat_1(esk2_0),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.12/0.40  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_38]), c_0_28])])).
% 0.12/0.40  cnf(c_0_45, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X3)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k2_xboole_0(X1,X3)),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.40  cnf(c_0_46, negated_conjecture, (~r1_tarski(k1_relat_1(esk2_0),k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.12/0.40  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),X1)|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_38]), c_0_28])])).
% 0.12/0.40  cnf(c_0_48, negated_conjecture, (~r1_tarski(k1_relat_1(esk3_0),k3_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.40  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.12/0.40  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38])]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 51
% 0.12/0.40  # Proof object clause steps            : 30
% 0.12/0.40  # Proof object formula steps           : 21
% 0.12/0.40  # Proof object conjectures             : 17
% 0.12/0.40  # Proof object clause conjectures      : 14
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 14
% 0.12/0.40  # Proof object initial formulas used   : 10
% 0.12/0.40  # Proof object generating inferences   : 14
% 0.12/0.40  # Proof object simplifying inferences  : 18
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 10
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 17
% 0.12/0.40  # Removed in clause preprocessing      : 0
% 0.12/0.40  # Initial clauses in saturation        : 17
% 0.12/0.40  # Processed clauses                    : 372
% 0.12/0.40  # ...of these trivial                  : 0
% 0.12/0.40  # ...subsumed                          : 213
% 0.12/0.40  # ...remaining for further processing  : 159
% 0.12/0.40  # Other redundant clauses eliminated   : 2
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 3
% 0.12/0.40  # Backward-rewritten                   : 4
% 0.12/0.40  # Generated clauses                    : 1465
% 0.12/0.40  # ...of the previous two non-trivial   : 1353
% 0.12/0.40  # Contextual simplify-reflections      : 0
% 0.12/0.40  # Paramodulations                      : 1463
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 2
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 134
% 0.12/0.40  #    Positive orientable unit clauses  : 18
% 0.12/0.40  #    Positive unorientable unit clauses: 0
% 0.12/0.40  #    Negative unit clauses             : 6
% 0.12/0.40  #    Non-unit-clauses                  : 110
% 0.12/0.40  # Current number of unprocessed clauses: 1006
% 0.12/0.40  # ...number of literals in the above   : 3805
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 23
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 4468
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 3032
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 215
% 0.12/0.40  # Unit Clause-clause subsumption calls : 175
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 18
% 0.12/0.40  # BW rewrite match successes           : 3
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 18889
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.058 s
% 0.12/0.40  # System time              : 0.004 s
% 0.12/0.40  # Total time               : 0.062 s
% 0.12/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
