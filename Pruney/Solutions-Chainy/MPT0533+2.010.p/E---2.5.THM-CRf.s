%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:13 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 144 expanded)
%              Number of clauses        :   31 (  58 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 617 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t133_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

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
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t133_relat_1])).

fof(c_0_6,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X24,X25)
      | k8_relat_1(X24,k8_relat_1(X25,X26)) = k8_relat_1(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_relat_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k8_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_10,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k8_relat_1(X5,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k8_relat_1(esk5_0,k8_relat_1(esk6_0,X1)) = k8_relat_1(esk5_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(X4,X3))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0)) = k8_relat_1(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k8_relat_1(X2,X4))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk6_0,esk7_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk5_0,esk7_0))
    | ~ v1_relat_1(k8_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),k8_relat_1(esk5_0,esk7_0))
    | ~ v1_relat_1(k8_relat_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X3,X1),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X5 != k8_relat_1(X2,X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k8_relat_1(esk5_0,esk7_0))
    | ~ v1_relat_1(k8_relat_1(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),k8_relat_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13]),c_0_15])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),k8_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | ~ r2_hidden(X2,X3)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk6_0)
    | ~ v1_relat_1(k8_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k8_relat_1(esk5_0,esk7_0))
    | ~ v1_relat_1(k8_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k8_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk3_2(X1,k8_relat_1(X2,X3)),esk4_2(X1,k8_relat_1(X2,X3))),X3)
    | ~ r2_hidden(esk4_2(X1,k8_relat_1(X2,X3)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_13]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(k8_relat_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_13]),c_0_15])])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.98  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.77/0.98  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.77/0.98  #
% 0.77/0.98  # Preprocessing time       : 0.027 s
% 0.77/0.98  # Presaturation interreduction done
% 0.77/0.98  
% 0.77/0.98  # Proof found!
% 0.77/0.98  # SZS status Theorem
% 0.77/0.98  # SZS output start CNFRefutation
% 0.77/0.98  fof(t133_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 0.77/0.98  fof(t130_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 0.77/0.98  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 0.77/0.98  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.77/0.98  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.77/0.98  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)))))), inference(assume_negation,[status(cth)],[t133_relat_1])).
% 0.77/0.98  fof(c_0_6, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X24,X25)|k8_relat_1(X24,k8_relat_1(X25,X26))=k8_relat_1(X24,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_relat_1])])).
% 0.77/0.98  fof(c_0_7, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&((r1_tarski(esk7_0,esk8_0)&r1_tarski(esk5_0,esk6_0))&~r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.77/0.98  fof(c_0_8, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X10,X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(X9,X10),X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(X12,X6)|~r2_hidden(k4_tarski(X11,X12),X7)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk2_3(X6,X7,X8),X6)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7))|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(esk2_3(X6,X7,X8),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.77/0.98  fof(c_0_9, plain, ![X22, X23]:(~v1_relat_1(X23)|v1_relat_1(k8_relat_1(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.77/0.98  cnf(c_0_10, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(X2,X1)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.77/0.98  cnf(c_0_11, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.77/0.98  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),X4)|X4!=k8_relat_1(X5,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.77/0.98  cnf(c_0_13, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.98  cnf(c_0_14, negated_conjecture, (k8_relat_1(esk5_0,k8_relat_1(esk6_0,X1))=k8_relat_1(esk5_0,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.77/0.98  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.77/0.98  fof(c_0_16, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(k4_tarski(X17,X18),X15)|r2_hidden(k4_tarski(X17,X18),X16))|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)|r1_tarski(X15,X19)|~v1_relat_1(X15))&(~r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)|r1_tarski(X15,X19)|~v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.77/0.98  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X4!=k8_relat_1(X2,X5)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.77/0.98  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k8_relat_1(X4,X3))|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])).
% 0.77/0.98  cnf(c_0_19, negated_conjecture, (k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0))=k8_relat_1(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.77/0.98  cnf(c_0_20, negated_conjecture, (~r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.77/0.98  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.77/0.98  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k8_relat_1(X2,X4))|~v1_relat_1(X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_13])).
% 0.77/0.98  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk6_0,esk7_0))|~r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk5_0,esk7_0))|~v1_relat_1(k8_relat_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.77/0.98  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),k8_relat_1(esk5_0,esk7_0))|~v1_relat_1(k8_relat_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.77/0.98  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X3,X1),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X5!=k8_relat_1(X2,X4)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.77/0.98  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(k4_tarski(X2,X1),k8_relat_1(esk5_0,esk7_0))|~v1_relat_1(k8_relat_1(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])])).
% 0.77/0.98  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),k8_relat_1(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_13]), c_0_15])])).
% 0.77/0.98  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.77/0.98  cnf(c_0_29, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.77/0.98  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.77/0.98  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),k8_relat_1(X3,X4))|~r2_hidden(k4_tarski(X1,X2),X4)|~r2_hidden(X2,X3)|~v1_relat_1(X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_13])).
% 0.77/0.98  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk6_0)|~v1_relat_1(k8_relat_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.77/0.98  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk8_0)|~r2_hidden(k4_tarski(X1,X2),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_15])])).
% 0.77/0.98  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_15])])).
% 0.77/0.98  cnf(c_0_35, negated_conjecture, (v1_relat_1(k8_relat_1(esk5_0,esk7_0))|~v1_relat_1(k8_relat_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 0.77/0.98  cnf(c_0_36, plain, (r1_tarski(X1,k8_relat_1(X2,X3))|~r2_hidden(k4_tarski(esk3_2(X1,k8_relat_1(X2,X3)),esk4_2(X1,k8_relat_1(X2,X3))),X3)|~r2_hidden(esk4_2(X1,k8_relat_1(X2,X3)),X2)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.77/0.98  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_13]), c_0_15])])).
% 0.77/0.98  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)),esk4_2(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))),esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.77/0.98  cnf(c_0_39, negated_conjecture, (v1_relat_1(k8_relat_1(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_13]), c_0_15])])).
% 0.77/0.98  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.77/0.98  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40])]), c_0_20]), ['proof']).
% 0.77/0.98  # SZS output end CNFRefutation
% 0.77/0.98  # Proof object total steps             : 42
% 0.77/0.98  # Proof object clause steps            : 31
% 0.77/0.98  # Proof object formula steps           : 11
% 0.77/0.98  # Proof object conjectures             : 22
% 0.77/0.98  # Proof object clause conjectures      : 19
% 0.77/0.98  # Proof object formula conjectures     : 3
% 0.77/0.98  # Proof object initial clauses used    : 13
% 0.77/0.98  # Proof object initial formulas used   : 5
% 0.77/0.98  # Proof object generating inferences   : 15
% 0.77/0.98  # Proof object simplifying inferences  : 23
% 0.77/0.98  # Training examples: 0 positive, 0 negative
% 0.77/0.98  # Parsed axioms                        : 5
% 0.77/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.98  # Initial clauses                      : 16
% 0.77/0.98  # Removed in clause preprocessing      : 0
% 0.77/0.98  # Initial clauses in saturation        : 16
% 0.77/0.98  # Processed clauses                    : 1780
% 0.77/0.98  # ...of these trivial                  : 31
% 0.77/0.98  # ...subsumed                          : 622
% 0.77/0.98  # ...remaining for further processing  : 1127
% 0.77/0.98  # Other redundant clauses eliminated   : 3
% 0.77/0.98  # Clauses deleted for lack of memory   : 0
% 0.77/0.98  # Backward-subsumed                    : 147
% 0.77/0.98  # Backward-rewritten                   : 250
% 0.77/0.98  # Generated clauses                    : 25848
% 0.77/0.98  # ...of the previous two non-trivial   : 24369
% 0.77/0.98  # Contextual simplify-reflections      : 39
% 0.77/0.98  # Paramodulations                      : 25807
% 0.77/0.98  # Factorizations                       : 38
% 0.77/0.98  # Equation resolutions                 : 3
% 0.77/0.98  # Propositional unsat checks           : 0
% 0.77/0.98  #    Propositional check models        : 0
% 0.77/0.98  #    Propositional check unsatisfiable : 0
% 0.77/0.98  #    Propositional clauses             : 0
% 0.77/0.98  #    Propositional clauses after purity: 0
% 0.77/0.98  #    Propositional unsat core size     : 0
% 0.77/0.98  #    Propositional preprocessing time  : 0.000
% 0.77/0.98  #    Propositional encoding time       : 0.000
% 0.77/0.98  #    Propositional solver time         : 0.000
% 0.77/0.98  #    Success case prop preproc time    : 0.000
% 0.77/0.98  #    Success case prop encoding time   : 0.000
% 0.77/0.98  #    Success case prop solver time     : 0.000
% 0.77/0.98  # Current number of processed clauses  : 711
% 0.77/0.98  #    Positive orientable unit clauses  : 260
% 0.77/0.98  #    Positive unorientable unit clauses: 0
% 0.77/0.98  #    Negative unit clauses             : 1
% 0.77/0.98  #    Non-unit-clauses                  : 450
% 0.77/0.98  # Current number of unprocessed clauses: 22420
% 0.77/0.98  # ...number of literals in the above   : 94942
% 0.77/0.98  # Current number of archived formulas  : 0
% 0.77/0.98  # Current number of archived clauses   : 413
% 0.77/0.98  # Clause-clause subsumption calls (NU) : 70901
% 0.77/0.98  # Rec. Clause-clause subsumption calls : 49016
% 0.77/0.98  # Non-unit clause-clause subsumptions  : 802
% 0.77/0.98  # Unit Clause-clause subsumption calls : 7006
% 0.77/0.98  # Rewrite failures with RHS unbound    : 0
% 0.77/0.98  # BW rewrite match attempts            : 4620
% 0.77/0.98  # BW rewrite match successes           : 224
% 0.77/0.98  # Condensation attempts                : 0
% 0.77/0.98  # Condensation successes               : 0
% 0.77/0.98  # Termbank termtop insertions          : 991269
% 0.83/0.99  
% 0.83/0.99  # -------------------------------------------------
% 0.83/0.99  # User time                : 0.631 s
% 0.83/0.99  # System time              : 0.013 s
% 0.83/0.99  # Total time               : 0.644 s
% 0.83/0.99  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
