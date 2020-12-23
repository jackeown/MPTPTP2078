%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:50 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
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
fof(t106_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

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
             => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_relat_1])).

fof(c_0_6,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X24,X25)
      | k7_relat_1(k7_relat_1(X26,X25),X24) = k7_relat_1(X26,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(k4_tarski(X11,X12),X6)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk1_3(X6,X7,X8),X7)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k7_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_10,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk6_0),esk5_0) = k7_relat_1(X1,esk5_0)
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
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk7_0,esk6_0),esk5_0) = k7_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(esk7_0,esk6_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(esk7_0,esk5_0))
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),k7_relat_1(esk7_0,esk5_0))
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(esk7_0,esk5_0))
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),k7_relat_1(esk7_0,esk5_0)) ),
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
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk6_0)
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk7_0,esk5_0))
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k7_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk3_2(X1,k7_relat_1(X2,X3)),esk4_2(X1,k7_relat_1(X2,X3))),X2)
    | ~ r2_hidden(esk3_2(X1,k7_relat_1(X2,X3)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_13]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk7_0,esk5_0)) ),
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
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:37:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.64/0.83  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.64/0.83  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.64/0.83  #
% 0.64/0.83  # Preprocessing time       : 0.026 s
% 0.64/0.83  # Presaturation interreduction done
% 0.64/0.83  
% 0.64/0.83  # Proof found!
% 0.64/0.83  # SZS status Theorem
% 0.64/0.83  # SZS output start CNFRefutation
% 0.64/0.83  fof(t106_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 0.64/0.83  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 0.64/0.83  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 0.64/0.83  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.64/0.83  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.64/0.83  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t106_relat_1])).
% 0.64/0.83  fof(c_0_6, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X24,X25)|k7_relat_1(k7_relat_1(X26,X25),X24)=k7_relat_1(X26,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 0.64/0.83  fof(c_0_7, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&((r1_tarski(esk7_0,esk8_0)&r1_tarski(esk5_0,esk6_0))&~r1_tarski(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.64/0.83  fof(c_0_8, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(X9,X10),X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&(~r2_hidden(X11,X7)|~r2_hidden(k4_tarski(X11,X12),X6)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk1_3(X6,X7,X8),X7)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6))|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&((r2_hidden(esk1_3(X6,X7,X8),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.64/0.83  fof(c_0_9, plain, ![X22, X23]:(~v1_relat_1(X22)|v1_relat_1(k7_relat_1(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.64/0.83  cnf(c_0_10, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.64/0.83  cnf(c_0_11, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.64/0.83  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),X4)|X4!=k7_relat_1(X3,X5)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.64/0.83  cnf(c_0_13, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.64/0.83  cnf(c_0_14, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk6_0),esk5_0)=k7_relat_1(X1,esk5_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.64/0.83  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.64/0.83  fof(c_0_16, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(k4_tarski(X17,X18),X15)|r2_hidden(k4_tarski(X17,X18),X16))|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)|r1_tarski(X15,X19)|~v1_relat_1(X15))&(~r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)|r1_tarski(X15,X19)|~v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.64/0.83  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k7_relat_1(X5,X2)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.64/0.83  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])).
% 0.64/0.83  cnf(c_0_19, negated_conjecture, (k7_relat_1(k7_relat_1(esk7_0,esk6_0),esk5_0)=k7_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.64/0.83  cnf(c_0_20, negated_conjecture, (~r1_tarski(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.64/0.83  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.64/0.83  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))|~v1_relat_1(X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_13])).
% 0.64/0.83  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(esk7_0,esk6_0))|~r2_hidden(k4_tarski(X1,X2),k7_relat_1(esk7_0,esk5_0))|~v1_relat_1(k7_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.64/0.83  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),k7_relat_1(esk7_0,esk5_0))|~v1_relat_1(k7_relat_1(esk7_0,esk5_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.64/0.83  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,X3),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X5!=k7_relat_1(X4,X2)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.64/0.83  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(k4_tarski(X1,X2),k7_relat_1(esk7_0,esk5_0))|~v1_relat_1(k7_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])])).
% 0.64/0.83  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),k7_relat_1(esk7_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_13]), c_0_15])])).
% 0.64/0.83  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.64/0.83  cnf(c_0_29, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.64/0.83  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.64/0.83  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_13])).
% 0.64/0.83  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk6_0)|~v1_relat_1(k7_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.64/0.83  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk8_0)|~r2_hidden(k4_tarski(X1,X2),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_15])])).
% 0.64/0.83  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_15])])).
% 0.64/0.83  cnf(c_0_35, negated_conjecture, (v1_relat_1(k7_relat_1(esk7_0,esk5_0))|~v1_relat_1(k7_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 0.64/0.83  cnf(c_0_36, plain, (r1_tarski(X1,k7_relat_1(X2,X3))|~r2_hidden(k4_tarski(esk3_2(X1,k7_relat_1(X2,X3)),esk4_2(X1,k7_relat_1(X2,X3))),X2)|~r2_hidden(esk3_2(X1,k7_relat_1(X2,X3)),X3)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.64/0.83  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_13]), c_0_15])])).
% 0.64/0.83  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0)),esk4_2(k7_relat_1(esk7_0,esk5_0),k7_relat_1(esk8_0,esk6_0))),esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.64/0.83  cnf(c_0_39, negated_conjecture, (v1_relat_1(k7_relat_1(esk7_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_13]), c_0_15])])).
% 0.64/0.83  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.64/0.83  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40])]), c_0_20]), ['proof']).
% 0.64/0.83  # SZS output end CNFRefutation
% 0.64/0.83  # Proof object total steps             : 42
% 0.64/0.83  # Proof object clause steps            : 31
% 0.64/0.83  # Proof object formula steps           : 11
% 0.64/0.83  # Proof object conjectures             : 22
% 0.64/0.83  # Proof object clause conjectures      : 19
% 0.64/0.83  # Proof object formula conjectures     : 3
% 0.64/0.83  # Proof object initial clauses used    : 13
% 0.64/0.83  # Proof object initial formulas used   : 5
% 0.64/0.83  # Proof object generating inferences   : 15
% 0.64/0.83  # Proof object simplifying inferences  : 23
% 0.64/0.83  # Training examples: 0 positive, 0 negative
% 0.64/0.83  # Parsed axioms                        : 5
% 0.64/0.83  # Removed by relevancy pruning/SinE    : 0
% 0.64/0.83  # Initial clauses                      : 16
% 0.64/0.83  # Removed in clause preprocessing      : 0
% 0.64/0.83  # Initial clauses in saturation        : 16
% 0.64/0.83  # Processed clauses                    : 1780
% 0.64/0.83  # ...of these trivial                  : 31
% 0.64/0.83  # ...subsumed                          : 620
% 0.64/0.83  # ...remaining for further processing  : 1129
% 0.64/0.83  # Other redundant clauses eliminated   : 3
% 0.64/0.83  # Clauses deleted for lack of memory   : 0
% 0.64/0.83  # Backward-subsumed                    : 148
% 0.64/0.83  # Backward-rewritten                   : 250
% 0.64/0.83  # Generated clauses                    : 25841
% 0.64/0.83  # ...of the previous two non-trivial   : 24359
% 0.64/0.83  # Contextual simplify-reflections      : 39
% 0.64/0.83  # Paramodulations                      : 25800
% 0.64/0.83  # Factorizations                       : 38
% 0.64/0.83  # Equation resolutions                 : 3
% 0.64/0.83  # Propositional unsat checks           : 0
% 0.64/0.83  #    Propositional check models        : 0
% 0.64/0.83  #    Propositional check unsatisfiable : 0
% 0.64/0.83  #    Propositional clauses             : 0
% 0.64/0.83  #    Propositional clauses after purity: 0
% 0.64/0.83  #    Propositional unsat core size     : 0
% 0.64/0.83  #    Propositional preprocessing time  : 0.000
% 0.64/0.83  #    Propositional encoding time       : 0.000
% 0.64/0.83  #    Propositional solver time         : 0.000
% 0.64/0.83  #    Success case prop preproc time    : 0.000
% 0.64/0.83  #    Success case prop encoding time   : 0.000
% 0.64/0.83  #    Success case prop solver time     : 0.000
% 0.64/0.83  # Current number of processed clauses  : 712
% 0.64/0.83  #    Positive orientable unit clauses  : 260
% 0.64/0.83  #    Positive unorientable unit clauses: 0
% 0.64/0.83  #    Negative unit clauses             : 1
% 0.64/0.83  #    Non-unit-clauses                  : 451
% 0.64/0.83  # Current number of unprocessed clauses: 22411
% 0.64/0.83  # ...number of literals in the above   : 94915
% 0.64/0.83  # Current number of archived formulas  : 0
% 0.64/0.83  # Current number of archived clauses   : 414
% 0.64/0.83  # Clause-clause subsumption calls (NU) : 71203
% 0.64/0.83  # Rec. Clause-clause subsumption calls : 49178
% 0.64/0.83  # Non-unit clause-clause subsumptions  : 801
% 0.64/0.83  # Unit Clause-clause subsumption calls : 7016
% 0.64/0.83  # Rewrite failures with RHS unbound    : 0
% 0.64/0.83  # BW rewrite match attempts            : 4618
% 0.64/0.83  # BW rewrite match successes           : 224
% 0.64/0.83  # Condensation attempts                : 0
% 0.64/0.83  # Condensation successes               : 0
% 0.64/0.83  # Termbank termtop insertions          : 990858
% 0.64/0.83  
% 0.64/0.83  # -------------------------------------------------
% 0.64/0.83  # User time                : 0.477 s
% 0.64/0.83  # System time              : 0.020 s
% 0.64/0.83  # Total time               : 0.498 s
% 0.64/0.83  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
