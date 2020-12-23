%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  91 expanded)
%              Number of clauses        :   25 (  39 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 228 expanded)
%              Number of equality atoms :   27 (  62 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t160_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t159_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k9_relat_1(k5_relat_1(X2,X3),X1) = k9_relat_1(X3,k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t160_relat_1])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | v1_relat_1(k5_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & k2_relat_1(k5_relat_1(esk2_0,esk3_0)) != k9_relat_1(esk3_0,k2_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k9_relat_1(k5_relat_1(X18,X19),X17) = k9_relat_1(X19,k9_relat_1(X18,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k9_relat_1(k5_relat_1(X1,X2),X3) = k9_relat_1(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k7_relat_1(k5_relat_1(X13,X14),X12) = k5_relat_1(k7_relat_1(X13,X12),X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(k1_relat_1(X21),X20)
      | k7_relat_1(X21,X20) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_19,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k9_relat_1(k5_relat_1(X1,esk3_0),X2) = k9_relat_1(esk3_0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_23,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1)) = k9_relat_1(k5_relat_1(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k9_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k9_relat_1(esk3_0,k9_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(k5_relat_1(X1,esk3_0),X2) = k5_relat_1(k7_relat_1(X1,X2),esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = esk2_0
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_15])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1)) = k9_relat_1(esk3_0,k9_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1) = k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0)) = k9_relat_1(esk3_0,k9_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk2_0,k1_relat_1(esk2_0)) = k2_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk2_0,esk3_0)) != k9_relat_1(esk3_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:16 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.19/0.53  # and selection function SelectSmallestOrientable.
% 0.19/0.53  #
% 0.19/0.53  # Preprocessing time       : 0.028 s
% 0.19/0.53  # Presaturation interreduction done
% 0.19/0.53  
% 0.19/0.53  # Proof found!
% 0.19/0.53  # SZS status Theorem
% 0.19/0.53  # SZS output start CNFRefutation
% 0.19/0.53  fof(t160_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 0.19/0.53  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.53  fof(t159_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k9_relat_1(k5_relat_1(X2,X3),X1)=k9_relat_1(X3,k9_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 0.19/0.53  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.53  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 0.19/0.53  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.53  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))))), inference(assume_negation,[status(cth)],[t160_relat_1])).
% 0.19/0.53  fof(c_0_8, plain, ![X10, X11]:(~v1_relat_1(X10)|~v1_relat_1(X11)|v1_relat_1(k5_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.53  fof(c_0_9, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&k2_relat_1(k5_relat_1(esk2_0,esk3_0))!=k9_relat_1(esk3_0,k2_relat_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.53  cnf(c_0_10, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.53  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.53  fof(c_0_12, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k9_relat_1(k5_relat_1(X18,X19),X17)=k9_relat_1(X19,k9_relat_1(X18,X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).
% 0.19/0.53  fof(c_0_13, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.53  cnf(c_0_14, negated_conjecture, (v1_relat_1(k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.53  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.53  cnf(c_0_16, plain, (k9_relat_1(k5_relat_1(X1,X2),X3)=k9_relat_1(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  fof(c_0_17, plain, ![X12, X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|k7_relat_1(k5_relat_1(X13,X14),X12)=k5_relat_1(k7_relat_1(X13,X12),X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.19/0.53  fof(c_0_18, plain, ![X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(k1_relat_1(X21),X20)|k7_relat_1(X21,X20)=X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.53  fof(c_0_19, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.53  cnf(c_0_20, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.53  cnf(c_0_21, negated_conjecture, (v1_relat_1(k5_relat_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.53  cnf(c_0_22, negated_conjecture, (k9_relat_1(k5_relat_1(X1,esk3_0),X2)=k9_relat_1(esk3_0,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_11])).
% 0.19/0.53  cnf(c_0_23, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_24, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.53  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.53  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.53  cnf(c_0_27, negated_conjecture, (k2_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1))=k9_relat_1(k5_relat_1(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.53  cnf(c_0_28, negated_conjecture, (k9_relat_1(k5_relat_1(esk2_0,esk3_0),X1)=k9_relat_1(esk3_0,k9_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_22, c_0_15])).
% 0.19/0.53  cnf(c_0_29, negated_conjecture, (k7_relat_1(k5_relat_1(X1,esk3_0),X2)=k5_relat_1(k7_relat_1(X1,X2),esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_11])).
% 0.19/0.53  cnf(c_0_30, negated_conjecture, (k7_relat_1(esk2_0,X1)=esk2_0|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_15])).
% 0.19/0.53  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.53  cnf(c_0_32, negated_conjecture, (k2_relat_1(k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1))=k9_relat_1(esk3_0,k9_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.53  cnf(c_0_33, negated_conjecture, (k7_relat_1(k5_relat_1(esk2_0,esk3_0),X1)=k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_15])).
% 0.19/0.53  cnf(c_0_34, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.19/0.53  cnf(c_0_35, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.53  cnf(c_0_36, negated_conjecture, (k2_relat_1(k5_relat_1(k7_relat_1(esk2_0,X1),esk3_0))=k9_relat_1(esk3_0,k9_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.53  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk2_0,k1_relat_1(esk2_0))=k2_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.53  cnf(c_0_38, negated_conjecture, (k2_relat_1(k5_relat_1(esk2_0,esk3_0))!=k9_relat_1(esk3_0,k2_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.53  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_37]), c_0_38]), ['proof']).
% 0.19/0.53  # SZS output end CNFRefutation
% 0.19/0.53  # Proof object total steps             : 40
% 0.19/0.53  # Proof object clause steps            : 25
% 0.19/0.53  # Proof object formula steps           : 15
% 0.19/0.53  # Proof object conjectures             : 20
% 0.19/0.53  # Proof object clause conjectures      : 17
% 0.19/0.53  # Proof object formula conjectures     : 3
% 0.19/0.53  # Proof object initial clauses used    : 10
% 0.19/0.53  # Proof object initial formulas used   : 7
% 0.19/0.53  # Proof object generating inferences   : 13
% 0.19/0.53  # Proof object simplifying inferences  : 4
% 0.19/0.53  # Training examples: 0 positive, 0 negative
% 0.19/0.53  # Parsed axioms                        : 7
% 0.19/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.53  # Initial clauses                      : 11
% 0.19/0.53  # Removed in clause preprocessing      : 0
% 0.19/0.53  # Initial clauses in saturation        : 11
% 0.19/0.53  # Processed clauses                    : 369
% 0.19/0.53  # ...of these trivial                  : 0
% 0.19/0.53  # ...subsumed                          : 1
% 0.19/0.53  # ...remaining for further processing  : 368
% 0.19/0.53  # Other redundant clauses eliminated   : 0
% 0.19/0.53  # Clauses deleted for lack of memory   : 0
% 0.19/0.53  # Backward-subsumed                    : 0
% 0.19/0.53  # Backward-rewritten                   : 12
% 0.19/0.53  # Generated clauses                    : 23477
% 0.19/0.53  # ...of the previous two non-trivial   : 23488
% 0.19/0.53  # Contextual simplify-reflections      : 0
% 0.19/0.53  # Paramodulations                      : 23477
% 0.19/0.53  # Factorizations                       : 0
% 0.19/0.53  # Equation resolutions                 : 0
% 0.19/0.53  # Propositional unsat checks           : 0
% 0.19/0.53  #    Propositional check models        : 0
% 0.19/0.53  #    Propositional check unsatisfiable : 0
% 0.19/0.53  #    Propositional clauses             : 0
% 0.19/0.53  #    Propositional clauses after purity: 0
% 0.19/0.53  #    Propositional unsat core size     : 0
% 0.19/0.53  #    Propositional preprocessing time  : 0.000
% 0.19/0.53  #    Propositional encoding time       : 0.000
% 0.19/0.53  #    Propositional solver time         : 0.000
% 0.19/0.53  #    Success case prop preproc time    : 0.000
% 0.19/0.53  #    Success case prop encoding time   : 0.000
% 0.19/0.53  #    Success case prop solver time     : 0.000
% 0.19/0.53  # Current number of processed clauses  : 345
% 0.19/0.53  #    Positive orientable unit clauses  : 207
% 0.19/0.53  #    Positive unorientable unit clauses: 0
% 0.19/0.53  #    Negative unit clauses             : 1
% 0.19/0.53  #    Non-unit-clauses                  : 137
% 0.19/0.53  # Current number of unprocessed clauses: 23141
% 0.19/0.53  # ...number of literals in the above   : 23757
% 0.19/0.53  # Current number of archived formulas  : 0
% 0.19/0.53  # Current number of archived clauses   : 23
% 0.19/0.53  # Clause-clause subsumption calls (NU) : 5775
% 0.19/0.53  # Rec. Clause-clause subsumption calls : 5774
% 0.19/0.53  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.53  # Unit Clause-clause subsumption calls : 3561
% 0.19/0.53  # Rewrite failures with RHS unbound    : 0
% 0.19/0.53  # BW rewrite match attempts            : 4663
% 0.19/0.53  # BW rewrite match successes           : 8
% 0.19/0.53  # Condensation attempts                : 0
% 0.19/0.53  # Condensation successes               : 0
% 0.19/0.53  # Termbank termtop insertions          : 483501
% 0.19/0.53  
% 0.19/0.53  # -------------------------------------------------
% 0.19/0.53  # User time                : 0.176 s
% 0.19/0.53  # System time              : 0.016 s
% 0.19/0.53  # Total time               : 0.192 s
% 0.19/0.53  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
