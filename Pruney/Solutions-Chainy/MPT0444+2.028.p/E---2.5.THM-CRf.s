%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:18 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 481 expanded)
%              Number of clauses        :   34 ( 242 expanded)
%              Number of leaves         :   11 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 (1102 expanded)
%              Number of equality atoms :   13 ( 232 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
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

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t27_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

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
    ! [X59,X60] :
      ( ( r1_tarski(k1_relat_1(X59),k1_relat_1(X60))
        | ~ r1_tarski(X59,X60)
        | ~ v1_relat_1(X60)
        | ~ v1_relat_1(X59) )
      & ( r1_tarski(k2_relat_1(X59),k2_relat_1(X60))
        | ~ r1_tarski(X59,X60)
        | ~ v1_relat_1(X60)
        | ~ v1_relat_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_35,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X53)
      | v1_relat_1(k3_xboole_0(X53,X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t27_relat_1])).

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
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k2_relat_1(X1))
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
    ( r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,X1)),k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,X1)),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_48]),c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k2_relat_1(esk3_0)))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relat_1(k3_xboole_0(X1,esk2_0)),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,esk2_0)),k3_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_51]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:34:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.80  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S064A
% 0.60/0.80  # and selection function SelectComplexG.
% 0.60/0.80  #
% 0.60/0.80  # Preprocessing time       : 0.028 s
% 0.60/0.80  # Presaturation interreduction done
% 0.60/0.80  
% 0.60/0.80  # Proof found!
% 0.60/0.80  # SZS status Theorem
% 0.60/0.80  # SZS output start CNFRefutation
% 0.60/0.80  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.60/0.80  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.60/0.80  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.60/0.80  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.60/0.80  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.60/0.80  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.60/0.80  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.60/0.80  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.60/0.80  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.60/0.80  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.60/0.80  fof(t27_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 0.60/0.80  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.60/0.80  fof(c_0_12, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|r1_xboole_0(X34,k4_xboole_0(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.60/0.80  cnf(c_0_13, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.80  fof(c_0_14, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.60/0.80  fof(c_0_15, plain, ![X17, X18]:r1_tarski(k3_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.60/0.80  fof(c_0_16, plain, ![X31, X32, X33]:(~r1_tarski(X31,k2_xboole_0(X32,X33))|~r1_xboole_0(X31,X33)|r1_tarski(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.60/0.80  cnf(c_0_17, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.60/0.80  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_13])).
% 0.60/0.80  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.80  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.80  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.60/0.80  cnf(c_0_22, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.60/0.80  cnf(c_0_23, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.60/0.80  fof(c_0_24, plain, ![X14, X15, X16]:(~r1_tarski(k2_xboole_0(X14,X15),X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.60/0.80  fof(c_0_25, plain, ![X23, X24, X25]:r1_tarski(k2_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X25)),k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.60/0.80  cnf(c_0_26, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.60/0.80  cnf(c_0_27, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.60/0.80  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.80  fof(c_0_29, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X19,X21)|r1_tarski(X19,k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.60/0.80  cnf(c_0_30, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.60/0.80  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.80  cnf(c_0_32, plain, (r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.60/0.80  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.60/0.80  fof(c_0_34, plain, ![X59, X60]:((r1_tarski(k1_relat_1(X59),k1_relat_1(X60))|~r1_tarski(X59,X60)|~v1_relat_1(X60)|~v1_relat_1(X59))&(r1_tarski(k2_relat_1(X59),k2_relat_1(X60))|~r1_tarski(X59,X60)|~v1_relat_1(X60)|~v1_relat_1(X59))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.60/0.80  fof(c_0_35, plain, ![X53, X54]:(~v1_relat_1(X53)|v1_relat_1(k3_xboole_0(X53,X54))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.60/0.80  fof(c_0_36, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t27_relat_1])).
% 0.60/0.80  cnf(c_0_37, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.60/0.80  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.60/0.80  cnf(c_0_39, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.60/0.80  cnf(c_0_40, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.80  cnf(c_0_41, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.60/0.80  fof(c_0_42, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.60/0.80  cnf(c_0_43, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_37, c_0_20])).
% 0.60/0.80  cnf(c_0_44, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.60/0.80  cnf(c_0_45, plain, (r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_20]), c_0_41])).
% 0.60/0.80  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.60/0.80  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.60/0.80  cnf(c_0_48, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.60/0.80  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,X1)),k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.60/0.80  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,X1)),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.60/0.80  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_48]), c_0_48])])).
% 0.60/0.80  cnf(c_0_52, negated_conjecture, (~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.60/0.80  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k2_relat_1(esk3_0)))|~r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_37, c_0_49])).
% 0.60/0.80  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_relat_1(k3_xboole_0(X1,esk2_0)),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.60/0.80  cnf(c_0_55, negated_conjecture, (~r1_tarski(k2_relat_1(k3_xboole_0(esk3_0,esk2_0)),k3_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_51]), c_0_51])).
% 0.60/0.80  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_51]), c_0_55]), ['proof']).
% 0.60/0.80  # SZS output end CNFRefutation
% 0.60/0.80  # Proof object total steps             : 57
% 0.60/0.80  # Proof object clause steps            : 34
% 0.60/0.80  # Proof object formula steps           : 23
% 0.60/0.80  # Proof object conjectures             : 12
% 0.60/0.80  # Proof object clause conjectures      : 9
% 0.60/0.80  # Proof object formula conjectures     : 3
% 0.60/0.80  # Proof object initial clauses used    : 14
% 0.60/0.80  # Proof object initial formulas used   : 11
% 0.60/0.80  # Proof object generating inferences   : 18
% 0.60/0.80  # Proof object simplifying inferences  : 10
% 0.60/0.80  # Training examples: 0 positive, 0 negative
% 0.60/0.80  # Parsed axioms                        : 25
% 0.60/0.80  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.80  # Initial clauses                      : 38
% 0.60/0.81  # Removed in clause preprocessing      : 0
% 0.60/0.81  # Initial clauses in saturation        : 38
% 0.60/0.81  # Processed clauses                    : 2698
% 0.60/0.81  # ...of these trivial                  : 357
% 0.60/0.81  # ...subsumed                          : 1115
% 0.60/0.81  # ...remaining for further processing  : 1226
% 0.60/0.81  # Other redundant clauses eliminated   : 7
% 0.60/0.81  # Clauses deleted for lack of memory   : 0
% 0.60/0.81  # Backward-subsumed                    : 13
% 0.60/0.81  # Backward-rewritten                   : 377
% 0.60/0.81  # Generated clauses                    : 38099
% 0.60/0.81  # ...of the previous two non-trivial   : 34165
% 0.60/0.81  # Contextual simplify-reflections      : 6
% 0.60/0.81  # Paramodulations                      : 38092
% 0.60/0.81  # Factorizations                       : 0
% 0.60/0.81  # Equation resolutions                 : 7
% 0.60/0.81  # Propositional unsat checks           : 0
% 0.60/0.81  #    Propositional check models        : 0
% 0.60/0.81  #    Propositional check unsatisfiable : 0
% 0.60/0.81  #    Propositional clauses             : 0
% 0.60/0.81  #    Propositional clauses after purity: 0
% 0.60/0.81  #    Propositional unsat core size     : 0
% 0.60/0.81  #    Propositional preprocessing time  : 0.000
% 0.60/0.81  #    Propositional encoding time       : 0.000
% 0.60/0.81  #    Propositional solver time         : 0.000
% 0.60/0.81  #    Success case prop preproc time    : 0.000
% 0.60/0.81  #    Success case prop encoding time   : 0.000
% 0.60/0.81  #    Success case prop solver time     : 0.000
% 0.60/0.81  # Current number of processed clauses  : 796
% 0.60/0.81  #    Positive orientable unit clauses  : 372
% 0.60/0.81  #    Positive unorientable unit clauses: 1
% 0.60/0.81  #    Negative unit clauses             : 1
% 0.60/0.81  #    Non-unit-clauses                  : 422
% 0.60/0.81  # Current number of unprocessed clauses: 31296
% 0.60/0.81  # ...number of literals in the above   : 128461
% 0.60/0.81  # Current number of archived formulas  : 0
% 0.60/0.81  # Current number of archived clauses   : 425
% 0.60/0.81  # Clause-clause subsumption calls (NU) : 52655
% 0.60/0.81  # Rec. Clause-clause subsumption calls : 16639
% 0.60/0.81  # Non-unit clause-clause subsumptions  : 1126
% 0.60/0.81  # Unit Clause-clause subsumption calls : 4935
% 0.60/0.81  # Rewrite failures with RHS unbound    : 0
% 0.60/0.81  # BW rewrite match attempts            : 26781
% 0.60/0.81  # BW rewrite match successes           : 462
% 0.60/0.81  # Condensation attempts                : 0
% 0.60/0.81  # Condensation successes               : 0
% 0.60/0.81  # Termbank termtop insertions          : 834065
% 0.60/0.81  
% 0.60/0.81  # -------------------------------------------------
% 0.60/0.81  # User time                : 0.446 s
% 0.60/0.81  # System time              : 0.025 s
% 0.60/0.81  # Total time               : 0.470 s
% 0.60/0.81  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
