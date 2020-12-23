%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:05 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  99 expanded)
%              Number of clauses        :   26 (  40 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 217 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t160_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | r1_tarski(k1_relat_1(k5_relat_1(X9,X10)),k1_relat_1(X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

fof(c_0_11,plain,(
    ! [X6] : v1_relat_1(k6_relat_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_12,plain,(
    ! [X16] :
      ( k1_relat_1(k6_relat_1(X16)) = X16
      & k2_relat_1(k6_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t160_relat_1])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k2_relat_1(k5_relat_1(esk1_0,esk2_0)) != k9_relat_1(esk2_0,k2_relat_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k7_relat_1(X19,X18) = k5_relat_1(k6_relat_1(X18),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_19,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X13,X14),X15) = k5_relat_1(X13,k5_relat_1(X14,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k2_relat_1(k7_relat_1(X8,X7)) = k9_relat_1(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_24,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | v1_relat_1(k5_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_25,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(k1_relat_1(X11),k2_relat_1(X12))
      | k2_relat_1(k5_relat_1(X12,X11)) = k2_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = k5_relat_1(k6_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_30,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk1_0,X1),X2) = k5_relat_1(esk1_0,k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k5_relat_1(X17,k6_relat_1(k2_relat_1(X17))) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_34,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_21]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk1_0,X1),esk2_0) = k5_relat_1(esk1_0,k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_39,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,k7_relat_1(esk2_0,k2_relat_1(X1)))) = k9_relat_1(esk2_0,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk1_0,k6_relat_1(X1)),esk2_0) = k5_relat_1(esk1_0,k5_relat_1(k6_relat_1(X1),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( k5_relat_1(esk1_0,k6_relat_1(k2_relat_1(esk1_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk1_0,k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0))) = k9_relat_1(esk2_0,k2_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( k5_relat_1(esk1_0,k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0)) = k5_relat_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk1_0,esk2_0)) != k9_relat_1(esk2_0,k2_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.56/0.75  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.56/0.75  # and selection function SelectVGNonCR.
% 0.56/0.75  #
% 0.56/0.75  # Preprocessing time       : 0.028 s
% 0.56/0.75  # Presaturation interreduction done
% 0.56/0.75  
% 0.56/0.75  # Proof found!
% 0.56/0.75  # SZS status Theorem
% 0.56/0.75  # SZS output start CNFRefutation
% 0.56/0.75  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 0.56/0.75  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.56/0.75  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.56/0.75  fof(t160_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 0.56/0.75  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.56/0.75  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.56/0.75  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.56/0.75  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.56/0.75  fof(t47_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X1),k2_relat_1(X2))=>k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 0.56/0.75  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.56/0.75  fof(c_0_10, plain, ![X9, X10]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|r1_tarski(k1_relat_1(k5_relat_1(X9,X10)),k1_relat_1(X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.56/0.75  fof(c_0_11, plain, ![X6]:v1_relat_1(k6_relat_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.56/0.75  fof(c_0_12, plain, ![X16]:(k1_relat_1(k6_relat_1(X16))=X16&k2_relat_1(k6_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.56/0.75  fof(c_0_13, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))))), inference(assume_negation,[status(cth)],[t160_relat_1])).
% 0.56/0.75  cnf(c_0_14, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.56/0.75  cnf(c_0_15, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.56/0.75  cnf(c_0_16, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.56/0.75  fof(c_0_17, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&k2_relat_1(k5_relat_1(esk1_0,esk2_0))!=k9_relat_1(esk2_0,k2_relat_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.56/0.75  fof(c_0_18, plain, ![X18, X19]:(~v1_relat_1(X19)|k7_relat_1(X19,X18)=k5_relat_1(k6_relat_1(X18),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.56/0.75  fof(c_0_19, plain, ![X13, X14, X15]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|(~v1_relat_1(X15)|k5_relat_1(k5_relat_1(X13,X14),X15)=k5_relat_1(X13,k5_relat_1(X14,X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.56/0.75  cnf(c_0_20, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.56/0.75  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.56/0.75  cnf(c_0_22, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.75  fof(c_0_23, plain, ![X7, X8]:(~v1_relat_1(X8)|k2_relat_1(k7_relat_1(X8,X7))=k9_relat_1(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.56/0.75  fof(c_0_24, plain, ![X4, X5]:(~v1_relat_1(X4)|~v1_relat_1(X5)|v1_relat_1(k5_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.56/0.75  cnf(c_0_25, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.56/0.75  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.56/0.75  fof(c_0_27, plain, ![X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|(~r1_tarski(k1_relat_1(X11),k2_relat_1(X12))|k2_relat_1(k5_relat_1(X12,X11))=k2_relat_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).
% 0.56/0.75  cnf(c_0_28, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),esk2_0)),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.56/0.75  cnf(c_0_29, negated_conjecture, (k7_relat_1(esk2_0,X1)=k5_relat_1(k6_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.56/0.75  cnf(c_0_30, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.56/0.75  cnf(c_0_31, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.75  cnf(c_0_32, negated_conjecture, (k5_relat_1(k5_relat_1(esk1_0,X1),X2)=k5_relat_1(esk1_0,k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.56/0.75  fof(c_0_33, plain, ![X17]:(~v1_relat_1(X17)|k5_relat_1(X17,k6_relat_1(k2_relat_1(X17)))=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.56/0.75  cnf(c_0_34, plain, (k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k2_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.56/0.75  cnf(c_0_35, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.56/0.75  cnf(c_0_36, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.56/0.75  cnf(c_0_37, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_21]), c_0_15])])).
% 0.56/0.75  cnf(c_0_38, negated_conjecture, (k5_relat_1(k5_relat_1(esk1_0,X1),esk2_0)=k5_relat_1(esk1_0,k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.56/0.75  cnf(c_0_39, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.56/0.75  cnf(c_0_40, negated_conjecture, (k2_relat_1(k5_relat_1(X1,k7_relat_1(esk2_0,k2_relat_1(X1))))=k9_relat_1(esk2_0,k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])])).
% 0.56/0.75  cnf(c_0_41, negated_conjecture, (k5_relat_1(k5_relat_1(esk1_0,k6_relat_1(X1)),esk2_0)=k5_relat_1(esk1_0,k5_relat_1(k6_relat_1(X1),esk2_0))), inference(spm,[status(thm)],[c_0_38, c_0_15])).
% 0.56/0.75  cnf(c_0_42, negated_conjecture, (k5_relat_1(esk1_0,k6_relat_1(k2_relat_1(esk1_0)))=esk1_0), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.56/0.75  cnf(c_0_43, negated_conjecture, (k2_relat_1(k5_relat_1(esk1_0,k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0)))=k9_relat_1(esk2_0,k2_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_26]), c_0_29])).
% 0.56/0.75  cnf(c_0_44, negated_conjecture, (k5_relat_1(esk1_0,k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0))=k5_relat_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.56/0.75  cnf(c_0_45, negated_conjecture, (k2_relat_1(k5_relat_1(esk1_0,esk2_0))!=k9_relat_1(esk2_0,k2_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.56/0.75  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45]), ['proof']).
% 0.56/0.75  # SZS output end CNFRefutation
% 0.56/0.75  # Proof object total steps             : 47
% 0.56/0.75  # Proof object clause steps            : 26
% 0.56/0.75  # Proof object formula steps           : 21
% 0.56/0.75  # Proof object conjectures             : 19
% 0.56/0.75  # Proof object clause conjectures      : 16
% 0.56/0.75  # Proof object formula conjectures     : 3
% 0.56/0.75  # Proof object initial clauses used    : 12
% 0.56/0.75  # Proof object initial formulas used   : 10
% 0.56/0.75  # Proof object generating inferences   : 13
% 0.56/0.75  # Proof object simplifying inferences  : 10
% 0.56/0.75  # Training examples: 0 positive, 0 negative
% 0.56/0.75  # Parsed axioms                        : 10
% 0.56/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.75  # Initial clauses                      : 13
% 0.56/0.75  # Removed in clause preprocessing      : 0
% 0.56/0.75  # Initial clauses in saturation        : 13
% 0.56/0.75  # Processed clauses                    : 986
% 0.56/0.75  # ...of these trivial                  : 66
% 0.56/0.75  # ...subsumed                          : 100
% 0.56/0.75  # ...remaining for further processing  : 820
% 0.56/0.75  # Other redundant clauses eliminated   : 0
% 0.56/0.75  # Clauses deleted for lack of memory   : 0
% 0.56/0.75  # Backward-subsumed                    : 4
% 0.56/0.75  # Backward-rewritten                   : 266
% 0.56/0.75  # Generated clauses                    : 47089
% 0.56/0.75  # ...of the previous two non-trivial   : 46929
% 0.56/0.75  # Contextual simplify-reflections      : 0
% 0.56/0.75  # Paramodulations                      : 47089
% 0.56/0.75  # Factorizations                       : 0
% 0.56/0.75  # Equation resolutions                 : 0
% 0.56/0.75  # Propositional unsat checks           : 0
% 0.56/0.75  #    Propositional check models        : 0
% 0.56/0.75  #    Propositional check unsatisfiable : 0
% 0.56/0.75  #    Propositional clauses             : 0
% 0.56/0.75  #    Propositional clauses after purity: 0
% 0.56/0.75  #    Propositional unsat core size     : 0
% 0.56/0.75  #    Propositional preprocessing time  : 0.000
% 0.56/0.75  #    Propositional encoding time       : 0.000
% 0.56/0.75  #    Propositional solver time         : 0.000
% 0.56/0.75  #    Success case prop preproc time    : 0.000
% 0.56/0.75  #    Success case prop encoding time   : 0.000
% 0.56/0.75  #    Success case prop solver time     : 0.000
% 0.56/0.75  # Current number of processed clauses  : 537
% 0.56/0.75  #    Positive orientable unit clauses  : 251
% 0.56/0.75  #    Positive unorientable unit clauses: 5
% 0.56/0.75  #    Negative unit clauses             : 1
% 0.56/0.75  #    Non-unit-clauses                  : 280
% 0.56/0.75  # Current number of unprocessed clauses: 45914
% 0.56/0.75  # ...number of literals in the above   : 80071
% 0.56/0.75  # Current number of archived formulas  : 0
% 0.56/0.75  # Current number of archived clauses   : 283
% 0.56/0.75  # Clause-clause subsumption calls (NU) : 7183
% 0.56/0.75  # Rec. Clause-clause subsumption calls : 7163
% 0.56/0.75  # Non-unit clause-clause subsumptions  : 101
% 0.56/0.75  # Unit Clause-clause subsumption calls : 1952
% 0.56/0.75  # Rewrite failures with RHS unbound    : 0
% 0.56/0.75  # BW rewrite match attempts            : 2990
% 0.56/0.75  # BW rewrite match successes           : 127
% 0.56/0.75  # Condensation attempts                : 0
% 0.56/0.75  # Condensation successes               : 0
% 0.56/0.75  # Termbank termtop insertions          : 1166538
% 0.56/0.76  
% 0.56/0.76  # -------------------------------------------------
% 0.56/0.76  # User time                : 0.386 s
% 0.56/0.76  # System time              : 0.031 s
% 0.56/0.76  # Total time               : 0.417 s
% 0.56/0.76  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
