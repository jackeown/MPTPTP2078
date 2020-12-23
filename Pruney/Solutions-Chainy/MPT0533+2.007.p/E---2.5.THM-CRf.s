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
% DateTime   : Thu Dec  3 10:50:13 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 103 expanded)
%              Number of clauses        :   27 (  42 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 422 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   18 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t133_relat_1])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_tarski(esk8_0,esk9_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(k4_tarski(X23,X24),X21)
        | r2_hidden(k4_tarski(X23,X24),X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X21)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X25)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X16,X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(X15,X16),X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X18,X12)
        | ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | ~ r2_hidden(esk3_3(X12,X13,X14),X12)
        | ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X13)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk3_3(X12,X13,X14),X12)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X13)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | v1_relat_1(k8_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_11,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | r1_tarski(k8_relat_1(X30,X31),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X3,X1),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X5 != k8_relat_1(X2,X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk6_0,esk8_0))
    | ~ v1_relat_1(k8_relat_1(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),k8_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),k8_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_21])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k8_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk7_0,X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_21])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk7_0,X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk7_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:17:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.50/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.50/0.65  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.50/0.65  #
% 0.50/0.65  # Preprocessing time       : 0.027 s
% 0.50/0.65  # Presaturation interreduction done
% 0.50/0.65  
% 0.50/0.65  # Proof found!
% 0.50/0.65  # SZS status Theorem
% 0.50/0.65  # SZS output start CNFRefutation
% 0.50/0.65  fof(t133_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 0.50/0.65  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.50/0.65  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 0.50/0.65  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.50/0.65  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.50/0.65  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 0.50/0.65  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)))))), inference(assume_negation,[status(cth)],[t133_relat_1])).
% 0.50/0.65  fof(c_0_7, negated_conjecture, (v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&((r1_tarski(esk8_0,esk9_0)&r1_tarski(esk6_0,esk7_0))&~r1_tarski(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.50/0.65  fof(c_0_8, plain, ![X21, X22, X23, X24, X25]:((~r1_tarski(X21,X22)|(~r2_hidden(k4_tarski(X23,X24),X21)|r2_hidden(k4_tarski(X23,X24),X22))|~v1_relat_1(X21))&((r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X21)|r1_tarski(X21,X25)|~v1_relat_1(X21))&(~r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X25)|r1_tarski(X21,X25)|~v1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.50/0.65  fof(c_0_9, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X16,X12)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k8_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13))&(r2_hidden(k4_tarski(X15,X16),X13)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k8_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)))&(~r2_hidden(X18,X12)|~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(k4_tarski(X17,X18),X14)|X14!=k8_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)))&((~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|(~r2_hidden(esk3_3(X12,X13,X14),X12)|~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X13))|X14=k8_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13))&((r2_hidden(esk3_3(X12,X13,X14),X12)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k8_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13))&(r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X13)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k8_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.50/0.65  fof(c_0_10, plain, ![X28, X29]:(~v1_relat_1(X29)|v1_relat_1(k8_relat_1(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.50/0.65  fof(c_0_11, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.50/0.65  cnf(c_0_12, negated_conjecture, (~r1_tarski(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.50/0.65  cnf(c_0_13, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.50/0.65  fof(c_0_14, plain, ![X30, X31]:(~v1_relat_1(X31)|r1_tarski(k8_relat_1(X30,X31),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.50/0.65  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X3,X1),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X5!=k8_relat_1(X2,X4)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.50/0.65  cnf(c_0_16, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.50/0.65  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.50/0.65  cnf(c_0_18, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.50/0.65  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X4!=k8_relat_1(X2,X5)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.50/0.65  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk6_0,esk8_0))|~v1_relat_1(k8_relat_1(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.50/0.65  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.50/0.65  cnf(c_0_22, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.65  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X2),k8_relat_1(X3,X4))|~v1_relat_1(X4)|~r2_hidden(k4_tarski(X1,X2),X4)|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_16])).
% 0.50/0.65  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.50/0.65  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),k8_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_16])).
% 0.50/0.65  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_21])])).
% 0.50/0.65  cnf(c_0_27, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.50/0.65  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~v1_relat_1(X2)|~r2_hidden(X1,k8_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.50/0.65  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k8_relat_1(esk7_0,X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.50/0.65  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_21])])).
% 0.50/0.65  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_17, c_0_27])).
% 0.50/0.65  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_21])])).
% 0.50/0.65  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(X1,esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk7_0,X2))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.50/0.65  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),esk9_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.50/0.65  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.50/0.65  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.50/0.65  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0)),esk5_2(k8_relat_1(esk6_0,esk8_0),k8_relat_1(esk7_0,esk9_0))),k8_relat_1(esk7_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.50/0.65  cnf(c_0_38, negated_conjecture, (~v1_relat_1(k8_relat_1(esk6_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_12])).
% 0.50/0.65  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_21])]), ['proof']).
% 0.50/0.65  # SZS output end CNFRefutation
% 0.50/0.65  # Proof object total steps             : 40
% 0.50/0.65  # Proof object clause steps            : 27
% 0.50/0.65  # Proof object formula steps           : 13
% 0.50/0.65  # Proof object conjectures             : 20
% 0.50/0.65  # Proof object clause conjectures      : 17
% 0.50/0.65  # Proof object formula conjectures     : 3
% 0.50/0.65  # Proof object initial clauses used    : 12
% 0.50/0.65  # Proof object initial formulas used   : 6
% 0.50/0.65  # Proof object generating inferences   : 13
% 0.50/0.65  # Proof object simplifying inferences  : 15
% 0.50/0.65  # Training examples: 0 positive, 0 negative
% 0.50/0.65  # Parsed axioms                        : 6
% 0.50/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.65  # Initial clauses                      : 19
% 0.50/0.65  # Removed in clause preprocessing      : 0
% 0.50/0.65  # Initial clauses in saturation        : 19
% 0.50/0.65  # Processed clauses                    : 1614
% 0.50/0.65  # ...of these trivial                  : 24
% 0.50/0.65  # ...subsumed                          : 482
% 0.50/0.65  # ...remaining for further processing  : 1108
% 0.50/0.65  # Other redundant clauses eliminated   : 3
% 0.50/0.65  # Clauses deleted for lack of memory   : 0
% 0.50/0.65  # Backward-subsumed                    : 73
% 0.50/0.65  # Backward-rewritten                   : 143
% 0.50/0.65  # Generated clauses                    : 14044
% 0.50/0.65  # ...of the previous two non-trivial   : 13360
% 0.50/0.65  # Contextual simplify-reflections      : 6
% 0.50/0.65  # Paramodulations                      : 14009
% 0.50/0.65  # Factorizations                       : 32
% 0.50/0.65  # Equation resolutions                 : 3
% 0.50/0.65  # Propositional unsat checks           : 0
% 0.50/0.65  #    Propositional check models        : 0
% 0.50/0.65  #    Propositional check unsatisfiable : 0
% 0.50/0.65  #    Propositional clauses             : 0
% 0.50/0.65  #    Propositional clauses after purity: 0
% 0.50/0.65  #    Propositional unsat core size     : 0
% 0.50/0.65  #    Propositional preprocessing time  : 0.000
% 0.50/0.65  #    Propositional encoding time       : 0.000
% 0.50/0.65  #    Propositional solver time         : 0.000
% 0.50/0.65  #    Success case prop preproc time    : 0.000
% 0.50/0.65  #    Success case prop encoding time   : 0.000
% 0.50/0.65  #    Success case prop solver time     : 0.000
% 0.50/0.65  # Current number of processed clauses  : 871
% 0.50/0.65  #    Positive orientable unit clauses  : 97
% 0.50/0.65  #    Positive unorientable unit clauses: 0
% 0.50/0.65  #    Negative unit clauses             : 2
% 0.50/0.65  #    Non-unit-clauses                  : 772
% 0.50/0.65  # Current number of unprocessed clauses: 11775
% 0.50/0.65  # ...number of literals in the above   : 51896
% 0.50/0.65  # Current number of archived formulas  : 0
% 0.50/0.65  # Current number of archived clauses   : 234
% 0.50/0.65  # Clause-clause subsumption calls (NU) : 132440
% 0.50/0.65  # Rec. Clause-clause subsumption calls : 64202
% 0.50/0.65  # Non-unit clause-clause subsumptions  : 560
% 0.50/0.65  # Unit Clause-clause subsumption calls : 2066
% 0.50/0.65  # Rewrite failures with RHS unbound    : 0
% 0.50/0.65  # BW rewrite match attempts            : 1031
% 0.50/0.65  # BW rewrite match successes           : 63
% 0.50/0.65  # Condensation attempts                : 0
% 0.50/0.65  # Condensation successes               : 0
% 0.50/0.65  # Termbank termtop insertions          : 375415
% 0.50/0.65  
% 0.50/0.65  # -------------------------------------------------
% 0.50/0.65  # User time                : 0.307 s
% 0.50/0.65  # System time              : 0.009 s
% 0.50/0.65  # Total time               : 0.317 s
% 0.50/0.65  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
