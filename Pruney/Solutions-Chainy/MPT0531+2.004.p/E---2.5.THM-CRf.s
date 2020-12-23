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
% DateTime   : Thu Dec  3 10:50:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  96 expanded)
%              Number of clauses        :   18 (  39 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 276 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t131_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(t130_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t131_relat_1])).

fof(c_0_6,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X24,X25)
      | k8_relat_1(X24,k8_relat_1(X25,X26)) = k8_relat_1(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_relat_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X10,X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(X9,X10),X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X12,X6)
        | ~ r2_hidden(k4_tarski(X11,X12),X7)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X6)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k8_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_12,negated_conjecture,
    ( k8_relat_1(esk5_0,k8_relat_1(esk6_0,X1)) = k8_relat_1(esk5_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k8_relat_1(X5,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0)) = k8_relat_1(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(X4,X3))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r1_tarski(X15,X16)
        | ~ r2_hidden(k4_tarski(X17,X18),X15)
        | r2_hidden(k4_tarski(X17,X18),X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)
        | r1_tarski(X15,X19)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)
        | r1_tarski(X15,X19)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(k8_relat_1(esk5_0,esk7_0))
    | ~ v1_relat_1(k8_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk6_0,esk7_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk5_0,esk7_0))
    | ~ v1_relat_1(k8_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(k8_relat_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_13])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk6_0,esk7_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_13])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0))),k8_relat_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0))),k8_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.19/0.46  # and selection function SelectCQIArNXTEqFirst.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.027 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t131_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_relat_1)).
% 0.19/0.46  fof(t130_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 0.19/0.46  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 0.19/0.46  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.19/0.46  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.19/0.46  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t131_relat_1])).
% 0.19/0.46  fof(c_0_6, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X24,X25)|k8_relat_1(X24,k8_relat_1(X25,X26))=k8_relat_1(X24,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_relat_1])])).
% 0.19/0.46  fof(c_0_7, negated_conjecture, (v1_relat_1(esk7_0)&(r1_tarski(esk5_0,esk6_0)&~r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.46  cnf(c_0_8, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(X2,X1)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.46  cnf(c_0_9, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.46  fof(c_0_10, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X10,X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(X9,X10),X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(X12,X6)|~r2_hidden(k4_tarski(X11,X12),X7)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk2_3(X6,X7,X8),X6)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7))|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(esk2_3(X6,X7,X8),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.19/0.46  fof(c_0_11, plain, ![X22, X23]:(~v1_relat_1(X23)|v1_relat_1(k8_relat_1(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.19/0.46  cnf(c_0_12, negated_conjecture, (k8_relat_1(esk5_0,k8_relat_1(esk6_0,X1))=k8_relat_1(esk5_0,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.46  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.46  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),X4)|X4!=k8_relat_1(X5,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_15, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  cnf(c_0_16, negated_conjecture, (k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0))=k8_relat_1(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.46  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k8_relat_1(X4,X3))|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_15])).
% 0.19/0.46  fof(c_0_18, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(k4_tarski(X17,X18),X15)|r2_hidden(k4_tarski(X17,X18),X16))|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)|r1_tarski(X15,X19)|~v1_relat_1(X15))&(~r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)|r1_tarski(X15,X19)|~v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.19/0.46  cnf(c_0_19, negated_conjecture, (v1_relat_1(k8_relat_1(esk5_0,esk7_0))|~v1_relat_1(k8_relat_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.46  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk6_0,esk7_0))|~r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk5_0,esk7_0))|~v1_relat_1(k8_relat_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.19/0.46  cnf(c_0_21, negated_conjecture, (~r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.46  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_23, negated_conjecture, (v1_relat_1(k8_relat_1(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_15]), c_0_13])])).
% 0.19/0.46  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk6_0,esk7_0))|~r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_15]), c_0_13])])).
% 0.19/0.46  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0))),k8_relat_1(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.19/0.46  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk7_0))),k8_relat_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.46  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23])]), c_0_21]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 29
% 0.19/0.46  # Proof object clause steps            : 18
% 0.19/0.46  # Proof object formula steps           : 11
% 0.19/0.46  # Proof object conjectures             : 15
% 0.19/0.46  # Proof object clause conjectures      : 12
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 8
% 0.19/0.46  # Proof object initial formulas used   : 5
% 0.19/0.46  # Proof object generating inferences   : 9
% 0.19/0.46  # Proof object simplifying inferences  : 11
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 5
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 14
% 0.19/0.46  # Removed in clause preprocessing      : 0
% 0.19/0.46  # Initial clauses in saturation        : 14
% 0.19/0.46  # Processed clauses                    : 450
% 0.19/0.46  # ...of these trivial                  : 5
% 0.19/0.46  # ...subsumed                          : 111
% 0.19/0.46  # ...remaining for further processing  : 334
% 0.19/0.46  # Other redundant clauses eliminated   : 3
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 36
% 0.19/0.46  # Backward-rewritten                   : 124
% 0.19/0.46  # Generated clauses                    : 3252
% 0.19/0.46  # ...of the previous two non-trivial   : 2813
% 0.19/0.46  # Contextual simplify-reflections      : 17
% 0.19/0.46  # Paramodulations                      : 3237
% 0.19/0.46  # Factorizations                       : 12
% 0.19/0.46  # Equation resolutions                 : 3
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 157
% 0.19/0.46  #    Positive orientable unit clauses  : 24
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 1
% 0.19/0.46  #    Non-unit-clauses                  : 132
% 0.19/0.46  # Current number of unprocessed clauses: 2304
% 0.19/0.46  # ...number of literals in the above   : 8377
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 174
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 7975
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 5187
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 164
% 0.19/0.46  # Unit Clause-clause subsumption calls : 1018
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 700
% 0.19/0.46  # BW rewrite match successes           : 37
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 148752
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.119 s
% 0.19/0.46  # System time              : 0.005 s
% 0.19/0.46  # Total time               : 0.124 s
% 0.19/0.46  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
