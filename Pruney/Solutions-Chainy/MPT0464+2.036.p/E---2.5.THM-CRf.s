%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:42 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 432 expanded)
%              Number of clauses        :   41 ( 207 expanded)
%              Number of leaves         :   12 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  126 ( 855 expanded)
%              Number of equality atoms :   21 ( 178 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,k2_xboole_0(X20,X21))
      | r1_tarski(k4_xboole_0(X19,X20),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_13,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

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
    ! [X17,X18] :
      ( ~ r1_tarski(X17,k4_xboole_0(X18,X17))
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_19,plain,(
    ! [X14,X15,X16] : r1_tarski(k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)),k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | X23 = k2_xboole_0(X22,k4_xboole_0(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_24,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X11,X13)
      | r1_tarski(X11,k3_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_25,plain,(
    ! [X9,X10] : r1_tarski(k3_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_39,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | ~ v1_relat_1(X30)
      | ~ r1_tarski(X28,X29)
      | r1_tarski(k5_relat_1(X30,X28),k5_relat_1(X30,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

fof(c_0_40,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k3_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_38])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_32])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_48,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_17]),c_0_43])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34])).

cnf(c_0_51,plain,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_49]),c_0_50]),c_0_34])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,X2)),k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_57])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k5_relat_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk2_0)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_43]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.06/2.22  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 2.06/2.22  # and selection function SelectDiffNegLit.
% 2.06/2.22  #
% 2.06/2.22  # Preprocessing time       : 0.027 s
% 2.06/2.22  # Presaturation interreduction done
% 2.06/2.22  
% 2.06/2.22  # Proof found!
% 2.06/2.22  # SZS status Theorem
% 2.06/2.22  # SZS output start CNFRefutation
% 2.06/2.22  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.06/2.22  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.06/2.22  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/2.22  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.06/2.22  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.06/2.22  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.06/2.22  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.06/2.22  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.06/2.22  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.06/2.22  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 2.06/2.22  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.06/2.22  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 2.06/2.22  fof(c_0_12, plain, ![X19, X20, X21]:(~r1_tarski(X19,k2_xboole_0(X20,X21))|r1_tarski(k4_xboole_0(X19,X20),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 2.06/2.22  fof(c_0_13, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.06/2.22  fof(c_0_14, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.06/2.22  fof(c_0_15, plain, ![X17, X18]:(~r1_tarski(X17,k4_xboole_0(X18,X17))|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 2.06/2.22  cnf(c_0_16, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.06/2.22  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.06/2.22  fof(c_0_18, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 2.06/2.22  fof(c_0_19, plain, ![X14, X15, X16]:r1_tarski(k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)),k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 2.06/2.22  fof(c_0_20, plain, ![X22, X23]:(~r1_tarski(X22,X23)|X23=k2_xboole_0(X22,k4_xboole_0(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 2.06/2.22  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.22  cnf(c_0_22, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.06/2.22  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 2.06/2.22  fof(c_0_24, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X11,X13)|r1_tarski(X11,k3_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 2.06/2.22  fof(c_0_25, plain, ![X9, X10]:r1_tarski(k3_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 2.06/2.22  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.06/2.22  cnf(c_0_27, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.06/2.22  cnf(c_0_28, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.06/2.22  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 2.06/2.22  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 2.06/2.22  cnf(c_0_31, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.06/2.22  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.06/2.22  cnf(c_0_33, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.06/2.22  cnf(c_0_34, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 2.06/2.22  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.06/2.22  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.06/2.22  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.22  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.06/2.22  fof(c_0_39, plain, ![X28, X29, X30]:(~v1_relat_1(X28)|(~v1_relat_1(X29)|(~v1_relat_1(X30)|(~r1_tarski(X28,X29)|r1_tarski(k5_relat_1(X30,X28),k5_relat_1(X30,X29)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 2.06/2.22  fof(c_0_40, plain, ![X26, X27]:(~v1_relat_1(X26)|v1_relat_1(k3_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 2.06/2.22  fof(c_0_41, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 2.06/2.22  cnf(c_0_42, plain, (r1_tarski(X1,k3_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 2.06/2.22  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_38])])).
% 2.06/2.22  cnf(c_0_44, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 2.06/2.22  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_32])).
% 2.06/2.22  cnf(c_0_46, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.06/2.22  cnf(c_0_47, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.06/2.22  fof(c_0_48, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 2.06/2.22  cnf(c_0_49, plain, (r1_tarski(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_17]), c_0_43])).
% 2.06/2.22  cnf(c_0_50, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_34])).
% 2.06/2.22  cnf(c_0_51, plain, (r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_47])).
% 2.06/2.22  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.06/2.22  cnf(c_0_53, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_49]), c_0_50]), c_0_34])).
% 2.06/2.22  cnf(c_0_54, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k3_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_28, c_0_32])).
% 2.06/2.22  cnf(c_0_55, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,X2)),k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.06/2.22  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.06/2.22  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.06/2.22  cnf(c_0_58, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_43])).
% 2.06/2.22  cnf(c_0_59, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.06/2.22  cnf(c_0_60, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_55, c_0_57])).
% 2.06/2.22  cnf(c_0_61, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_43])).
% 2.06/2.22  cnf(c_0_62, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k5_relat_1(esk1_0,esk3_0)))|~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_31, c_0_59])).
% 2.06/2.22  cnf(c_0_63, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk2_0)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 2.06/2.22  cnf(c_0_64, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.06/2.22  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_43]), c_0_64]), ['proof']).
% 2.06/2.22  # SZS output end CNFRefutation
% 2.06/2.22  # Proof object total steps             : 66
% 2.06/2.22  # Proof object clause steps            : 41
% 2.06/2.22  # Proof object formula steps           : 25
% 2.06/2.22  # Proof object conjectures             : 13
% 2.06/2.22  # Proof object clause conjectures      : 10
% 2.06/2.22  # Proof object formula conjectures     : 3
% 2.06/2.22  # Proof object initial clauses used    : 16
% 2.06/2.22  # Proof object initial formulas used   : 12
% 2.06/2.22  # Proof object generating inferences   : 24
% 2.06/2.22  # Proof object simplifying inferences  : 12
% 2.06/2.22  # Training examples: 0 positive, 0 negative
% 2.06/2.22  # Parsed axioms                        : 12
% 2.06/2.22  # Removed by relevancy pruning/SinE    : 0
% 2.06/2.22  # Initial clauses                      : 17
% 2.06/2.22  # Removed in clause preprocessing      : 0
% 2.06/2.22  # Initial clauses in saturation        : 17
% 2.06/2.22  # Processed clauses                    : 10170
% 2.06/2.22  # ...of these trivial                  : 3185
% 2.06/2.22  # ...subsumed                          : 3810
% 2.06/2.22  # ...remaining for further processing  : 3175
% 2.06/2.22  # Other redundant clauses eliminated   : 2
% 2.06/2.22  # Clauses deleted for lack of memory   : 0
% 2.06/2.22  # Backward-subsumed                    : 5
% 2.06/2.22  # Backward-rewritten                   : 127
% 2.06/2.22  # Generated clauses                    : 266927
% 2.06/2.22  # ...of the previous two non-trivial   : 226759
% 2.06/2.22  # Contextual simplify-reflections      : 1
% 2.06/2.22  # Paramodulations                      : 266925
% 2.06/2.22  # Factorizations                       : 0
% 2.06/2.22  # Equation resolutions                 : 2
% 2.06/2.22  # Propositional unsat checks           : 0
% 2.06/2.22  #    Propositional check models        : 0
% 2.06/2.22  #    Propositional check unsatisfiable : 0
% 2.06/2.22  #    Propositional clauses             : 0
% 2.06/2.22  #    Propositional clauses after purity: 0
% 2.06/2.22  #    Propositional unsat core size     : 0
% 2.06/2.22  #    Propositional preprocessing time  : 0.000
% 2.06/2.22  #    Propositional encoding time       : 0.000
% 2.06/2.22  #    Propositional solver time         : 0.000
% 2.06/2.22  #    Success case prop preproc time    : 0.000
% 2.06/2.22  #    Success case prop encoding time   : 0.000
% 2.06/2.22  #    Success case prop solver time     : 0.000
% 2.06/2.22  # Current number of processed clauses  : 3025
% 2.06/2.22  #    Positive orientable unit clauses  : 1949
% 2.06/2.22  #    Positive unorientable unit clauses: 1
% 2.06/2.22  #    Negative unit clauses             : 1
% 2.06/2.22  #    Non-unit-clauses                  : 1074
% 2.06/2.22  # Current number of unprocessed clauses: 216103
% 2.06/2.22  # ...number of literals in the above   : 251112
% 2.06/2.22  # Current number of archived formulas  : 0
% 2.06/2.22  # Current number of archived clauses   : 148
% 2.06/2.22  # Clause-clause subsumption calls (NU) : 81983
% 2.06/2.22  # Rec. Clause-clause subsumption calls : 77985
% 2.06/2.22  # Non-unit clause-clause subsumptions  : 3788
% 2.06/2.22  # Unit Clause-clause subsumption calls : 15660
% 2.06/2.22  # Rewrite failures with RHS unbound    : 0
% 2.06/2.22  # BW rewrite match attempts            : 33288
% 2.06/2.22  # BW rewrite match successes           : 162
% 2.06/2.22  # Condensation attempts                : 0
% 2.06/2.22  # Condensation successes               : 0
% 2.06/2.22  # Termbank termtop insertions          : 5011757
% 2.06/2.23  
% 2.06/2.23  # -------------------------------------------------
% 2.06/2.23  # User time                : 1.782 s
% 2.06/2.23  # System time              : 0.107 s
% 2.06/2.23  # Total time               : 1.889 s
% 2.06/2.23  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
