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
% DateTime   : Thu Dec  3 10:48:09 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 360 expanded)
%              Number of clauses        :   37 ( 181 expanded)
%              Number of leaves         :    9 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 827 expanded)
%              Number of equality atoms :   21 ( 248 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t14_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X20,X22)
      | r1_tarski(X20,k3_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X30,X31] : r1_tarski(X30,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,plain,(
    ! [X26,X27,X28] : r1_tarski(k2_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)),k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

fof(c_0_22,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X58)
      | v1_relat_1(k3_xboole_0(X58,X59)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_xboole_0(k2_xboole_0(X1,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,k3_xboole_0(X18,X19))
      | r1_tarski(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t14_relat_1])).

cnf(c_0_28,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | ~ v1_relat_1(X61)
      | k1_relat_1(k2_xboole_0(X60,X61)) = k2_xboole_0(k1_relat_1(X60),k1_relat_1(X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_relat_1(esk5_0)
    & ~ r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_36,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk4_0)) = k1_relat_1(k2_xboole_0(X1,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk5_0)) = k1_relat_1(k2_xboole_0(X1,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(esk4_0,X1)),k1_relat_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(X1,esk5_0)),k1_relat_1(esk5_0)) = k1_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_46]),c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,X1)),k3_xboole_0(X2,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X1,esk5_0)),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(esk5_0,esk4_0)),k3_xboole_0(k1_relat_1(esk5_0),k1_relat_1(esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_51]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.53/2.70  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S015I
% 2.53/2.70  # and selection function PSelectOptimalLit.
% 2.53/2.70  #
% 2.53/2.70  # Preprocessing time       : 0.028 s
% 2.53/2.70  # Presaturation interreduction done
% 2.53/2.70  
% 2.53/2.70  # Proof found!
% 2.53/2.70  # SZS status Theorem
% 2.53/2.70  # SZS output start CNFRefutation
% 2.53/2.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/2.70  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.53/2.70  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.53/2.70  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.53/2.70  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.53/2.70  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.53/2.70  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.53/2.70  fof(t14_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 2.53/2.70  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 2.53/2.70  fof(c_0_9, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.53/2.70  fof(c_0_10, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_tarski(X20,X22)|r1_tarski(X20,k3_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 2.53/2.70  cnf(c_0_11, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.53/2.70  fof(c_0_12, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.53/2.70  cnf(c_0_13, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.53/2.70  cnf(c_0_14, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_11])).
% 2.53/2.70  fof(c_0_15, plain, ![X30, X31]:r1_tarski(X30,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.53/2.70  fof(c_0_16, plain, ![X26, X27, X28]:r1_tarski(k2_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)),k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 2.53/2.70  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.53/2.70  cnf(c_0_18, plain, (r1_tarski(X1,k3_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 2.53/2.70  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.53/2.70  cnf(c_0_20, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.53/2.70  cnf(c_0_21, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 2.53/2.70  fof(c_0_22, plain, ![X58, X59]:(~v1_relat_1(X58)|v1_relat_1(k3_xboole_0(X58,X59))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 2.53/2.70  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.53/2.70  cnf(c_0_24, plain, (r1_tarski(X1,k3_xboole_0(k2_xboole_0(X1,X2),X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 2.53/2.70  cnf(c_0_25, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 2.53/2.70  fof(c_0_26, plain, ![X17, X18, X19]:(~r1_tarski(X17,k3_xboole_0(X18,X19))|r1_tarski(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 2.53/2.70  fof(c_0_27, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t14_relat_1])).
% 2.53/2.70  cnf(c_0_28, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.53/2.70  cnf(c_0_29, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 2.53/2.70  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.53/2.70  fof(c_0_31, plain, ![X60, X61]:(~v1_relat_1(X60)|(~v1_relat_1(X61)|k1_relat_1(k2_xboole_0(X60,X61))=k2_xboole_0(k1_relat_1(X60),k1_relat_1(X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 2.53/2.71  fof(c_0_32, negated_conjecture, (v1_relat_1(esk4_0)&(v1_relat_1(esk5_0)&~r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 2.53/2.71  cnf(c_0_33, plain, (v1_relat_1(X1)|~v1_relat_1(k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.53/2.71  cnf(c_0_34, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 2.53/2.71  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_14])).
% 2.53/2.71  cnf(c_0_36, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.53/2.71  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.53/2.71  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.53/2.71  cnf(c_0_39, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.53/2.71  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_13, c_0_35])).
% 2.53/2.71  cnf(c_0_41, negated_conjecture, (k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk4_0))=k1_relat_1(k2_xboole_0(X1,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 2.53/2.71  cnf(c_0_42, negated_conjecture, (v1_relat_1(k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 2.53/2.71  cnf(c_0_43, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_17, c_0_35])).
% 2.53/2.71  cnf(c_0_44, negated_conjecture, (k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk5_0))=k1_relat_1(k2_xboole_0(X1,esk5_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_38])).
% 2.53/2.71  cnf(c_0_45, negated_conjecture, (v1_relat_1(k3_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 2.53/2.71  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 2.53/2.71  cnf(c_0_47, plain, (r1_tarski(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 2.53/2.71  cnf(c_0_48, negated_conjecture, (k2_xboole_0(k1_relat_1(k3_xboole_0(esk4_0,X1)),k1_relat_1(esk4_0))=k1_relat_1(esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 2.53/2.71  cnf(c_0_49, negated_conjecture, (k2_xboole_0(k1_relat_1(k3_xboole_0(X1,esk5_0)),k1_relat_1(esk5_0))=k1_relat_1(esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_34])).
% 2.53/2.71  cnf(c_0_50, negated_conjecture, (~r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.53/2.71  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_46]), c_0_46])])).
% 2.53/2.71  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,X1)),k3_xboole_0(X2,k1_relat_1(esk4_0)))|~r1_tarski(k1_relat_1(k3_xboole_0(esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 2.53/2.71  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_relat_1(k3_xboole_0(X1,esk5_0)),k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_19, c_0_49])).
% 2.53/2.71  cnf(c_0_54, negated_conjecture, (~r1_tarski(k1_relat_1(k3_xboole_0(esk5_0,esk4_0)),k3_xboole_0(k1_relat_1(esk5_0),k1_relat_1(esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_51])).
% 2.53/2.71  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_51]), c_0_54]), ['proof']).
% 2.53/2.71  # SZS output end CNFRefutation
% 2.53/2.71  # Proof object total steps             : 56
% 2.53/2.71  # Proof object clause steps            : 37
% 2.53/2.71  # Proof object formula steps           : 19
% 2.53/2.71  # Proof object conjectures             : 16
% 2.53/2.71  # Proof object clause conjectures      : 13
% 2.53/2.71  # Proof object formula conjectures     : 3
% 2.53/2.71  # Proof object initial clauses used    : 12
% 2.53/2.71  # Proof object initial formulas used   : 9
% 2.53/2.71  # Proof object generating inferences   : 23
% 2.53/2.71  # Proof object simplifying inferences  : 12
% 2.53/2.71  # Training examples: 0 positive, 0 negative
% 2.53/2.71  # Parsed axioms                        : 23
% 2.53/2.71  # Removed by relevancy pruning/SinE    : 0
% 2.53/2.71  # Initial clauses                      : 37
% 2.53/2.71  # Removed in clause preprocessing      : 0
% 2.53/2.71  # Initial clauses in saturation        : 37
% 2.53/2.71  # Processed clauses                    : 24338
% 2.53/2.71  # ...of these trivial                  : 2751
% 2.53/2.71  # ...subsumed                          : 17483
% 2.53/2.71  # ...remaining for further processing  : 4104
% 2.53/2.71  # Other redundant clauses eliminated   : 4
% 2.53/2.71  # Clauses deleted for lack of memory   : 0
% 2.53/2.71  # Backward-subsumed                    : 6
% 2.53/2.71  # Backward-rewritten                   : 96
% 2.53/2.71  # Generated clauses                    : 345759
% 2.53/2.71  # ...of the previous two non-trivial   : 243486
% 2.53/2.71  # Contextual simplify-reflections      : 0
% 2.53/2.71  # Paramodulations                      : 345753
% 2.53/2.71  # Factorizations                       : 2
% 2.53/2.71  # Equation resolutions                 : 4
% 2.53/2.71  # Propositional unsat checks           : 0
% 2.53/2.71  #    Propositional check models        : 0
% 2.53/2.71  #    Propositional check unsatisfiable : 0
% 2.53/2.71  #    Propositional clauses             : 0
% 2.53/2.71  #    Propositional clauses after purity: 0
% 2.53/2.71  #    Propositional unsat core size     : 0
% 2.53/2.71  #    Propositional preprocessing time  : 0.000
% 2.53/2.71  #    Propositional encoding time       : 0.000
% 2.53/2.71  #    Propositional solver time         : 0.000
% 2.53/2.71  #    Success case prop preproc time    : 0.000
% 2.53/2.71  #    Success case prop encoding time   : 0.000
% 2.53/2.71  #    Success case prop solver time     : 0.000
% 2.53/2.71  # Current number of processed clauses  : 3962
% 2.53/2.71  #    Positive orientable unit clauses  : 2203
% 2.53/2.71  #    Positive unorientable unit clauses: 1
% 2.53/2.71  #    Negative unit clauses             : 1
% 2.53/2.71  #    Non-unit-clauses                  : 1757
% 2.53/2.71  # Current number of unprocessed clauses: 218254
% 2.53/2.71  # ...number of literals in the above   : 297910
% 2.53/2.71  # Current number of archived formulas  : 0
% 2.53/2.71  # Current number of archived clauses   : 138
% 2.53/2.71  # Clause-clause subsumption calls (NU) : 1303494
% 2.53/2.71  # Rec. Clause-clause subsumption calls : 1048726
% 2.53/2.71  # Non-unit clause-clause subsumptions  : 17489
% 2.53/2.71  # Unit Clause-clause subsumption calls : 23224
% 2.53/2.71  # Rewrite failures with RHS unbound    : 0
% 2.53/2.71  # BW rewrite match attempts            : 10376
% 2.53/2.71  # BW rewrite match successes           : 297
% 2.53/2.71  # Condensation attempts                : 0
% 2.53/2.71  # Condensation successes               : 0
% 2.53/2.71  # Termbank termtop insertions          : 4802420
% 2.53/2.72  
% 2.53/2.72  # -------------------------------------------------
% 2.53/2.72  # User time                : 2.266 s
% 2.53/2.72  # System time              : 0.107 s
% 2.53/2.72  # Total time               : 2.373 s
% 2.53/2.72  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
