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
% DateTime   : Thu Dec  3 10:54:32 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   38 (  71 expanded)
%              Number of clauses        :   21 (  30 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 168 expanded)
%              Number of equality atoms :   28 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(t139_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_8,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | v1_relat_1(k5_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_9,plain,(
    ! [X26,X28] :
      ( v1_relat_1(esk2_1(X26))
      & v1_funct_1(esk2_1(X26))
      & k1_relat_1(esk2_1(X26)) = X26
      & ( ~ r2_hidden(X28,X26)
        | k1_funct_1(esk2_1(X26),X28) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t139_funct_1])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | k1_relat_1(k5_relat_1(X16,X17)) = k10_relat_1(X16,k1_relat_1(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & k10_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0) != k3_xboole_0(esk3_0,k10_relat_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k7_relat_1(k5_relat_1(X14,X15),X13) = k5_relat_1(k7_relat_1(X14,X13),X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k1_relat_1(k7_relat_1(X22,X21)) = k3_xboole_0(k1_relat_1(X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_20,plain,
    ( v1_relat_1(k5_relat_1(X1,esk2_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_relat_1(k5_relat_1(X1,esk2_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_16])).

cnf(c_0_23,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk5_0,esk2_1(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk5_0,esk2_1(X1))) = k10_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_28,plain,
    ( k7_relat_1(k5_relat_1(X1,esk2_1(X2)),X3) = k5_relat_1(k7_relat_1(X1,X3),esk2_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k5_relat_1(esk5_0,esk2_1(X1)),X2)) = k3_xboole_0(k10_relat_1(esk5_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk5_0,esk2_1(X1)),X2) = k5_relat_1(k7_relat_1(esk5_0,X2),esk2_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k7_relat_1(esk5_0,X1),esk2_1(X2))) = k10_relat_1(k7_relat_1(esk5_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_29])).

fof(c_0_33,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0) != k3_xboole_0(esk3_0,k10_relat_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk5_0,X1),X2) = k3_xboole_0(k10_relat_1(esk5_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.87/1.07  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.87/1.07  # and selection function SelectDiffNegLit.
% 0.87/1.07  #
% 0.87/1.07  # Preprocessing time       : 0.028 s
% 0.87/1.07  # Presaturation interreduction done
% 0.87/1.07  
% 0.87/1.07  # Proof found!
% 0.87/1.07  # SZS status Theorem
% 0.87/1.07  # SZS output start CNFRefutation
% 0.87/1.07  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.87/1.07  fof(s3_funct_1__e9_44_1__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 0.87/1.07  fof(t139_funct_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.87/1.07  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.87/1.07  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.87/1.07  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.87/1.07  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.87/1.07  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.87/1.07  fof(c_0_8, plain, ![X9, X10]:(~v1_relat_1(X9)|~v1_relat_1(X10)|v1_relat_1(k5_relat_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.87/1.07  fof(c_0_9, plain, ![X26, X28]:(((v1_relat_1(esk2_1(X26))&v1_funct_1(esk2_1(X26)))&k1_relat_1(esk2_1(X26))=X26)&(~r2_hidden(X28,X26)|k1_funct_1(esk2_1(X26),X28)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).
% 0.87/1.07  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t139_funct_1])).
% 0.87/1.07  fof(c_0_11, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|k1_relat_1(k5_relat_1(X16,X17))=k10_relat_1(X16,k1_relat_1(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.87/1.07  cnf(c_0_12, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.87/1.07  cnf(c_0_13, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.87/1.07  fof(c_0_14, negated_conjecture, (v1_relat_1(esk5_0)&k10_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0)!=k3_xboole_0(esk3_0,k10_relat_1(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.87/1.07  cnf(c_0_15, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.87/1.07  cnf(c_0_16, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.87/1.07  fof(c_0_17, plain, ![X13, X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k7_relat_1(k5_relat_1(X14,X15),X13)=k5_relat_1(k7_relat_1(X14,X13),X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.87/1.07  fof(c_0_18, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.87/1.07  fof(c_0_19, plain, ![X21, X22]:(~v1_relat_1(X22)|k1_relat_1(k7_relat_1(X22,X21))=k3_xboole_0(k1_relat_1(X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.87/1.07  cnf(c_0_20, plain, (v1_relat_1(k5_relat_1(X1,esk2_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.87/1.07  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.07  cnf(c_0_22, plain, (k1_relat_1(k5_relat_1(X1,esk2_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_16])).
% 0.87/1.07  cnf(c_0_23, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.87/1.07  cnf(c_0_24, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.87/1.07  cnf(c_0_25, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.87/1.07  cnf(c_0_26, negated_conjecture, (v1_relat_1(k5_relat_1(esk5_0,esk2_1(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.87/1.07  cnf(c_0_27, negated_conjecture, (k1_relat_1(k5_relat_1(esk5_0,esk2_1(X1)))=k10_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.87/1.07  cnf(c_0_28, plain, (k7_relat_1(k5_relat_1(X1,esk2_1(X2)),X3)=k5_relat_1(k7_relat_1(X1,X3),esk2_1(X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_13])).
% 0.87/1.07  cnf(c_0_29, negated_conjecture, (v1_relat_1(k7_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.87/1.07  cnf(c_0_30, negated_conjecture, (k1_relat_1(k7_relat_1(k5_relat_1(esk5_0,esk2_1(X1)),X2))=k3_xboole_0(k10_relat_1(esk5_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.87/1.07  cnf(c_0_31, negated_conjecture, (k7_relat_1(k5_relat_1(esk5_0,esk2_1(X1)),X2)=k5_relat_1(k7_relat_1(esk5_0,X2),esk2_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.87/1.07  cnf(c_0_32, negated_conjecture, (k1_relat_1(k5_relat_1(k7_relat_1(esk5_0,X1),esk2_1(X2)))=k10_relat_1(k7_relat_1(esk5_0,X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_29])).
% 0.87/1.07  fof(c_0_33, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.87/1.07  cnf(c_0_34, negated_conjecture, (k10_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0)!=k3_xboole_0(esk3_0,k10_relat_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.07  cnf(c_0_35, negated_conjecture, (k10_relat_1(k7_relat_1(esk5_0,X1),X2)=k3_xboole_0(k10_relat_1(esk5_0,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.87/1.07  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.87/1.07  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), ['proof']).
% 0.87/1.07  # SZS output end CNFRefutation
% 0.87/1.07  # Proof object total steps             : 38
% 0.87/1.07  # Proof object clause steps            : 21
% 0.87/1.07  # Proof object formula steps           : 17
% 0.87/1.07  # Proof object conjectures             : 13
% 0.87/1.07  # Proof object clause conjectures      : 10
% 0.87/1.07  # Proof object formula conjectures     : 3
% 0.87/1.07  # Proof object initial clauses used    : 10
% 0.87/1.07  # Proof object initial formulas used   : 8
% 0.87/1.07  # Proof object generating inferences   : 9
% 0.87/1.07  # Proof object simplifying inferences  : 7
% 0.87/1.07  # Training examples: 0 positive, 0 negative
% 0.87/1.07  # Parsed axioms                        : 12
% 0.87/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.87/1.07  # Initial clauses                      : 19
% 0.87/1.07  # Removed in clause preprocessing      : 0
% 0.87/1.07  # Initial clauses in saturation        : 19
% 0.87/1.07  # Processed clauses                    : 812
% 0.87/1.07  # ...of these trivial                  : 2
% 0.87/1.07  # ...subsumed                          : 38
% 0.87/1.07  # ...remaining for further processing  : 772
% 0.87/1.07  # Other redundant clauses eliminated   : 0
% 0.87/1.07  # Clauses deleted for lack of memory   : 0
% 0.87/1.07  # Backward-subsumed                    : 0
% 0.87/1.07  # Backward-rewritten                   : 75
% 0.87/1.07  # Generated clauses                    : 110387
% 0.87/1.07  # ...of the previous two non-trivial   : 110420
% 0.87/1.07  # Contextual simplify-reflections      : 0
% 0.87/1.07  # Paramodulations                      : 110383
% 0.87/1.07  # Factorizations                       : 0
% 0.87/1.07  # Equation resolutions                 : 4
% 0.87/1.07  # Propositional unsat checks           : 0
% 0.87/1.07  #    Propositional check models        : 0
% 0.87/1.07  #    Propositional check unsatisfiable : 0
% 0.87/1.07  #    Propositional clauses             : 0
% 0.87/1.07  #    Propositional clauses after purity: 0
% 0.87/1.07  #    Propositional unsat core size     : 0
% 0.87/1.07  #    Propositional preprocessing time  : 0.000
% 0.87/1.07  #    Propositional encoding time       : 0.000
% 0.87/1.07  #    Propositional solver time         : 0.000
% 0.87/1.07  #    Success case prop preproc time    : 0.000
% 0.87/1.07  #    Success case prop encoding time   : 0.000
% 0.87/1.07  #    Success case prop solver time     : 0.000
% 0.87/1.07  # Current number of processed clauses  : 678
% 0.87/1.07  #    Positive orientable unit clauses  : 337
% 0.87/1.07  #    Positive unorientable unit clauses: 1
% 0.87/1.07  #    Negative unit clauses             : 0
% 0.87/1.07  #    Non-unit-clauses                  : 340
% 0.87/1.07  # Current number of unprocessed clauses: 109614
% 0.87/1.07  # ...number of literals in the above   : 121144
% 0.87/1.07  # Current number of archived formulas  : 0
% 0.87/1.07  # Current number of archived clauses   : 94
% 0.87/1.07  # Clause-clause subsumption calls (NU) : 12271
% 0.87/1.07  # Rec. Clause-clause subsumption calls : 12106
% 0.87/1.07  # Non-unit clause-clause subsumptions  : 38
% 0.87/1.07  # Unit Clause-clause subsumption calls : 4441
% 0.87/1.07  # Rewrite failures with RHS unbound    : 0
% 0.87/1.07  # BW rewrite match attempts            : 4295
% 0.87/1.07  # BW rewrite match successes           : 34
% 0.87/1.07  # Condensation attempts                : 0
% 0.87/1.07  # Condensation successes               : 0
% 0.87/1.07  # Termbank termtop insertions          : 2004985
% 0.87/1.08  
% 0.87/1.08  # -------------------------------------------------
% 0.87/1.08  # User time                : 0.666 s
% 0.87/1.08  # System time              : 0.065 s
% 0.87/1.08  # Total time               : 0.731 s
% 0.87/1.08  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
