%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:51 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   37 (  68 expanded)
%              Number of clauses        :   22 (  28 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 208 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(t105_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_relat_1])).

fof(c_0_8,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | v1_relat_1(k7_relat_1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k7_relat_1(esk3_0,esk1_0),k7_relat_1(esk4_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | r1_tarski(k1_relat_1(k7_relat_1(X14,X13)),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(k1_relat_1(X18),X17)
      | k7_relat_1(X18,X17) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_13,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(k7_relat_1(X16,X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_19,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(k7_relat_1(X11,X10),k7_relat_1(X12,X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).

cnf(c_0_20,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),X2) = k7_relat_1(esk3_0,X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk3_0,esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk3_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(esk4_0,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) = k7_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk3_0,esk1_0),k7_relat_1(esk4_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21]),c_0_34])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:10:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.15/0.38  # and selection function PSelectSmallestOrientable.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.026 s
% 0.15/0.38  # Presaturation interreduction done
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(t106_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 0.15/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.15/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.15/0.38  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.15/0.39  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.15/0.39  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.15/0.39  fof(t105_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 0.15/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t106_relat_1])).
% 0.15/0.39  fof(c_0_8, plain, ![X8, X9]:(~v1_relat_1(X8)|v1_relat_1(k7_relat_1(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.15/0.39  fof(c_0_9, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk1_0,esk2_0))&~r1_tarski(k7_relat_1(esk3_0,esk1_0),k7_relat_1(esk4_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.15/0.39  fof(c_0_10, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.15/0.39  fof(c_0_11, plain, ![X13, X14]:(~v1_relat_1(X14)|r1_tarski(k1_relat_1(k7_relat_1(X14,X13)),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.15/0.39  fof(c_0_12, plain, ![X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(k1_relat_1(X18),X17)|k7_relat_1(X18,X17)=X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.15/0.39  cnf(c_0_13, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  cnf(c_0_16, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_17, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.39  fof(c_0_18, plain, ![X15, X16]:(~v1_relat_1(X16)|r1_tarski(k7_relat_1(X16,X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.15/0.39  fof(c_0_19, plain, ![X10, X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|(~r1_tarski(X11,X12)|r1_tarski(k7_relat_1(X11,X10),k7_relat_1(X12,X10))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).
% 0.15/0.39  cnf(c_0_20, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.39  cnf(c_0_21, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.15/0.39  cnf(c_0_22, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.39  cnf(c_0_23, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X1)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.15/0.39  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_25, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.39  cnf(c_0_26, plain, (r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.39  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_28, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),X2)=k7_relat_1(esk3_0,X1)|~r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.15/0.39  cnf(c_0_29, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk3_0,esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.15/0.39  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_24])).
% 0.15/0.39  cnf(c_0_31, negated_conjecture, (r1_tarski(k7_relat_1(esk3_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_14])).
% 0.15/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(k7_relat_1(X1,X2),k7_relat_1(esk4_0,X2))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.15/0.39  cnf(c_0_33, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)=k7_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.15/0.39  cnf(c_0_34, negated_conjecture, (r1_tarski(k7_relat_1(esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.15/0.39  cnf(c_0_35, negated_conjecture, (~r1_tarski(k7_relat_1(esk3_0,esk1_0),k7_relat_1(esk4_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_21]), c_0_34])]), c_0_35]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 37
% 0.15/0.39  # Proof object clause steps            : 22
% 0.15/0.39  # Proof object formula steps           : 15
% 0.15/0.39  # Proof object conjectures             : 19
% 0.15/0.39  # Proof object clause conjectures      : 16
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 11
% 0.15/0.39  # Proof object initial formulas used   : 7
% 0.15/0.39  # Proof object generating inferences   : 11
% 0.15/0.39  # Proof object simplifying inferences  : 4
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 7
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 11
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 11
% 0.15/0.39  # Processed clauses                    : 92
% 0.15/0.39  # ...of these trivial                  : 10
% 0.15/0.39  # ...subsumed                          : 0
% 0.15/0.39  # ...remaining for further processing  : 82
% 0.15/0.39  # Other redundant clauses eliminated   : 0
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 1
% 0.15/0.39  # Backward-rewritten                   : 2
% 0.15/0.39  # Generated clauses                    : 224
% 0.15/0.39  # ...of the previous two non-trivial   : 173
% 0.15/0.39  # Contextual simplify-reflections      : 0
% 0.15/0.39  # Paramodulations                      : 224
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 0
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 68
% 0.15/0.39  #    Positive orientable unit clauses  : 47
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 1
% 0.15/0.39  #    Non-unit-clauses                  : 20
% 0.15/0.39  # Current number of unprocessed clauses: 101
% 0.15/0.39  # ...number of literals in the above   : 186
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 14
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 36
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 34
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.39  # Unit Clause-clause subsumption calls : 2
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 78
% 0.15/0.39  # BW rewrite match successes           : 3
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 4009
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.031 s
% 0.15/0.39  # System time              : 0.004 s
% 0.15/0.39  # Total time               : 0.034 s
% 0.15/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
