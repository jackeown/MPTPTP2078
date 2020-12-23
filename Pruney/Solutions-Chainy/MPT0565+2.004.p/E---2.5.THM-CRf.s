%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:11 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   24 (  82 expanded)
%              Number of clauses        :   15 (  34 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 310 expanded)
%              Number of equality atoms :   15 (  65 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t169_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_4,plain,(
    ! [X16,X17,X18,X20] :
      ( ( r2_hidden(esk4_3(X16,X17,X18),k2_relat_1(X18))
        | ~ r2_hidden(X16,k10_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(X16,esk4_3(X16,X17,X18)),X18)
        | ~ r2_hidden(X16,k10_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk4_3(X16,X17,X18),X17)
        | ~ r2_hidden(X16,k10_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X20,k2_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X20),X18)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X16,k10_relat_1(X18,X17))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_5,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(X21,k1_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(X22,k2_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)
        | X12 = k1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)
        | X12 = k1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t169_relat_1])).

cnf(c_0_8,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & k10_relat_1(esk5_0,k2_relat_1(esk5_0)) != k1_relat_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),k2_relat_1(X2))
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk2_2(X2,X1),k10_relat_1(X2,X3))
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_2(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( X1 = k1_relat_1(esk5_0)
    | r2_hidden(esk3_2(esk5_0,X1),k2_relat_1(esk5_0))
    | r2_hidden(esk2_2(esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( X1 = k1_relat_1(esk5_0)
    | r2_hidden(esk2_2(esk5_0,X1),k10_relat_1(esk5_0,k2_relat_1(esk5_0)))
    | r2_hidden(esk2_2(esk5_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_14])])).

cnf(c_0_18,negated_conjecture,
    ( k10_relat_1(esk5_0,k2_relat_1(esk5_0)) != k1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k10_relat_1(esk5_0,k2_relat_1(esk5_0))),k10_relat_1(esk5_0,k2_relat_1(esk5_0))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_2(esk5_0,k10_relat_1(esk5_0,k2_relat_1(esk5_0))),X1),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_14])]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:56:21 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.11/0.36  # and selection function SelectVGNonCR.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.027 s
% 0.11/0.36  # Presaturation interreduction done
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.11/0.36  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.11/0.36  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.11/0.36  fof(t169_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.11/0.36  fof(c_0_4, plain, ![X16, X17, X18, X20]:((((r2_hidden(esk4_3(X16,X17,X18),k2_relat_1(X18))|~r2_hidden(X16,k10_relat_1(X18,X17))|~v1_relat_1(X18))&(r2_hidden(k4_tarski(X16,esk4_3(X16,X17,X18)),X18)|~r2_hidden(X16,k10_relat_1(X18,X17))|~v1_relat_1(X18)))&(r2_hidden(esk4_3(X16,X17,X18),X17)|~r2_hidden(X16,k10_relat_1(X18,X17))|~v1_relat_1(X18)))&(~r2_hidden(X20,k2_relat_1(X18))|~r2_hidden(k4_tarski(X16,X20),X18)|~r2_hidden(X20,X17)|r2_hidden(X16,k10_relat_1(X18,X17))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.11/0.36  fof(c_0_5, plain, ![X21, X22, X23]:((r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|~v1_relat_1(X23))&(r2_hidden(X22,k2_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.11/0.36  fof(c_0_6, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)|X6!=k1_relat_1(X5))&(~r2_hidden(k4_tarski(X9,X10),X5)|r2_hidden(X9,X6)|X6!=k1_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)|X12=k1_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)|X12=k1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.11/0.36  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1))), inference(assume_negation,[status(cth)],[t169_relat_1])).
% 0.11/0.36  cnf(c_0_8, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.11/0.36  cnf(c_0_9, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.11/0.36  cnf(c_0_10, plain, (r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  fof(c_0_11, negated_conjecture, (v1_relat_1(esk5_0)&k10_relat_1(esk5_0,k2_relat_1(esk5_0))!=k1_relat_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.11/0.36  cnf(c_0_12, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_8, c_0_9])).
% 0.11/0.36  cnf(c_0_13, plain, (X1=k1_relat_1(X2)|r2_hidden(esk3_2(X2,X1),k2_relat_1(X2))|r2_hidden(esk2_2(X2,X1),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.11/0.36  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_15, plain, (X1=k1_relat_1(X2)|r2_hidden(esk2_2(X2,X1),k10_relat_1(X2,X3))|r2_hidden(esk2_2(X2,X1),X1)|~v1_relat_1(X2)|~r2_hidden(esk3_2(X2,X1),X3)), inference(spm,[status(thm)],[c_0_12, c_0_10])).
% 0.11/0.36  cnf(c_0_16, negated_conjecture, (X1=k1_relat_1(esk5_0)|r2_hidden(esk3_2(esk5_0,X1),k2_relat_1(esk5_0))|r2_hidden(esk2_2(esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.11/0.36  cnf(c_0_17, negated_conjecture, (X1=k1_relat_1(esk5_0)|r2_hidden(esk2_2(esk5_0,X1),k10_relat_1(esk5_0,k2_relat_1(esk5_0)))|r2_hidden(esk2_2(esk5_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_14])])).
% 0.11/0.36  cnf(c_0_18, negated_conjecture, (k10_relat_1(esk5_0,k2_relat_1(esk5_0))!=k1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_19, plain, (X2=k1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_2(esk5_0,k10_relat_1(esk5_0,k2_relat_1(esk5_0))),k10_relat_1(esk5_0,k2_relat_1(esk5_0)))), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_17]), c_0_18])).
% 0.11/0.36  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.11/0.36  cnf(c_0_22, negated_conjecture, (~r2_hidden(k4_tarski(esk2_2(esk5_0,k10_relat_1(esk5_0,k2_relat_1(esk5_0))),X1),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_18])).
% 0.11/0.36  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_14])]), c_0_22]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 24
% 0.11/0.36  # Proof object clause steps            : 15
% 0.11/0.36  # Proof object formula steps           : 9
% 0.11/0.36  # Proof object conjectures             : 10
% 0.11/0.36  # Proof object clause conjectures      : 7
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 7
% 0.11/0.36  # Proof object initial formulas used   : 4
% 0.11/0.36  # Proof object generating inferences   : 7
% 0.11/0.36  # Proof object simplifying inferences  : 8
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 4
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 12
% 0.11/0.36  # Removed in clause preprocessing      : 0
% 0.11/0.36  # Initial clauses in saturation        : 12
% 0.11/0.36  # Processed clauses                    : 56
% 0.11/0.36  # ...of these trivial                  : 4
% 0.11/0.36  # ...subsumed                          : 1
% 0.11/0.36  # ...remaining for further processing  : 50
% 0.11/0.36  # Other redundant clauses eliminated   : 0
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 1
% 0.11/0.36  # Backward-rewritten                   : 0
% 0.11/0.36  # Generated clauses                    : 65
% 0.11/0.36  # ...of the previous two non-trivial   : 62
% 0.11/0.36  # Contextual simplify-reflections      : 1
% 0.11/0.36  # Paramodulations                      : 53
% 0.11/0.36  # Factorizations                       : 4
% 0.11/0.36  # Equation resolutions                 : 8
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 37
% 0.11/0.36  #    Positive orientable unit clauses  : 3
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 3
% 0.11/0.36  #    Non-unit-clauses                  : 31
% 0.11/0.36  # Current number of unprocessed clauses: 29
% 0.11/0.36  # ...number of literals in the above   : 113
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 13
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 67
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 21
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 3
% 0.11/0.36  # Unit Clause-clause subsumption calls : 1
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 0
% 0.11/0.36  # BW rewrite match successes           : 0
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 2551
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.029 s
% 0.11/0.36  # System time              : 0.006 s
% 0.11/0.36  # Total time               : 0.034 s
% 0.11/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
