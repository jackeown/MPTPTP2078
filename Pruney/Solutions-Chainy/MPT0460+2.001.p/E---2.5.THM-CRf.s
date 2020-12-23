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
% DateTime   : Thu Dec  3 10:48:36 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 117 expanded)
%              Number of clauses        :   24 (  43 expanded)
%              Number of leaves         :    4 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 568 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relat_1])).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(k4_tarski(X11,X12),X9)
        | r2_hidden(k4_tarski(X11,X12),X10)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(esk1_2(X9,X13),esk2_2(X9,X13)),X9)
        | r1_tarski(X9,X13)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X9,X13),esk2_2(X9,X13)),X13)
        | r1_tarski(X9,X13)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X19,X20,X22,X23,X24,X27] :
      ( ( r2_hidden(k4_tarski(X19,esk3_5(X16,X17,X18,X19,X20)),X16)
        | ~ r2_hidden(k4_tarski(X19,X20),X18)
        | X18 != k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk3_5(X16,X17,X18,X19,X20),X20),X17)
        | ~ r2_hidden(k4_tarski(X19,X20),X18)
        | X18 != k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X22,X24),X16)
        | ~ r2_hidden(k4_tarski(X24,X23),X17)
        | r2_hidden(k4_tarski(X22,X23),X18)
        | X18 != k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18)),X18)
        | ~ r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X27),X16)
        | ~ r2_hidden(k4_tarski(X27,esk5_3(X16,X17,X18)),X17)
        | X18 = k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk6_3(X16,X17,X18)),X16)
        | r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18)),X18)
        | X18 = k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk6_3(X16,X17,X18),esk5_3(X16,X17,X18)),X17)
        | r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18)),X18)
        | X18 = k5_relat_1(X16,X17)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_relat_1(X30)
      | v1_relat_1(k5_relat_1(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_5(X1,esk7_0,k5_relat_1(X1,esk7_0),X2,X3),X3),esk8_0)
    | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,esk7_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_11])])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(esk9_0,esk7_0))
    | ~ v1_relat_1(k5_relat_1(esk9_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,esk8_0))
    | ~ r2_hidden(k4_tarski(X1,esk3_5(X4,esk7_0,k5_relat_1(X4,esk7_0),X5,X2)),X3)
    | ~ r2_hidden(k4_tarski(X5,X2),k5_relat_1(X4,esk7_0))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(esk9_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_13]),c_0_11]),c_0_23])])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(X2,esk8_0))
    | ~ r2_hidden(k4_tarski(X1,esk3_5(esk9_0,esk7_0,k5_relat_1(esk9_0,esk7_0),esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)))),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_23])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_13])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23]),c_0_25]),c_0_11])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk9_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_13]),c_0_11]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t48_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 0.13/0.38  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.13/0.38  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.13/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))))))), inference(assume_negation,[status(cth)],[t48_relat_1])).
% 0.13/0.38  fof(c_0_5, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(k4_tarski(X11,X12),X9)|r2_hidden(k4_tarski(X11,X12),X10))|~v1_relat_1(X9))&((r2_hidden(k4_tarski(esk1_2(X9,X13),esk2_2(X9,X13)),X9)|r1_tarski(X9,X13)|~v1_relat_1(X9))&(~r2_hidden(k4_tarski(esk1_2(X9,X13),esk2_2(X9,X13)),X13)|r1_tarski(X9,X13)|~v1_relat_1(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.13/0.38  fof(c_0_6, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&(r1_tarski(esk7_0,esk8_0)&~r1_tarski(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X16, X17, X18, X19, X20, X22, X23, X24, X27]:((((r2_hidden(k4_tarski(X19,esk3_5(X16,X17,X18,X19,X20)),X16)|~r2_hidden(k4_tarski(X19,X20),X18)|X18!=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk3_5(X16,X17,X18,X19,X20),X20),X17)|~r2_hidden(k4_tarski(X19,X20),X18)|X18!=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(X22,X24),X16)|~r2_hidden(k4_tarski(X24,X23),X17)|r2_hidden(k4_tarski(X22,X23),X18)|X18!=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16)))&((~r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18)),X18)|(~r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X27),X16)|~r2_hidden(k4_tarski(X27,esk5_3(X16,X17,X18)),X17))|X18=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))&((r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk6_3(X16,X17,X18)),X16)|r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18)),X18)|X18=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk6_3(X16,X17,X18),esk5_3(X16,X17,X18)),X17)|r2_hidden(k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18)),X18)|X18=k5_relat_1(X16,X17)|~v1_relat_1(X18)|~v1_relat_1(X17)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X29, X30]:(~v1_relat_1(X29)|~v1_relat_1(X30)|v1_relat_1(k5_relat_1(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.38  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_13, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk8_0)|~r2_hidden(k4_tarski(X1,X2),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.13/0.38  cnf(c_0_16, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (~r1_tarski(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_18, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_13])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk3_5(X1,esk7_0,k5_relat_1(X1,esk7_0),X2,X3),X3),esk8_0)|~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,esk7_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_11])])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(esk9_0,esk7_0))|~v1_relat_1(k5_relat_1(esk9_0,esk7_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,esk8_0))|~r2_hidden(k4_tarski(X1,esk3_5(X4,esk7_0,k5_relat_1(X4,esk7_0),X5,X2)),X3)|~r2_hidden(k4_tarski(X5,X2),k5_relat_1(X4,esk7_0))|~v1_relat_1(X3)|~v1_relat_1(X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(esk9_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_13]), c_0_11]), c_0_23])])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(X2,esk8_0))|~r2_hidden(k4_tarski(X1,esk3_5(esk9_0,esk7_0,k5_relat_1(esk9_0,esk7_0),esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)))),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_23])])).
% 0.13/0.38  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_13])).
% 0.13/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0)),esk2_2(k5_relat_1(esk9_0,esk7_0),k5_relat_1(esk9_0,esk8_0))),k5_relat_1(esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23]), c_0_25]), c_0_11])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~v1_relat_1(k5_relat_1(esk9_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_17])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_13]), c_0_11]), c_0_23])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 33
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 9
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 4
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 25
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 18
% 0.13/0.38  # Processed clauses                    : 71
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 70
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 1
% 0.13/0.38  # Generated clauses                    : 244
% 0.13/0.38  # ...of the previous two non-trivial   : 240
% 0.13/0.38  # Contextual simplify-reflections      : 8
% 0.13/0.38  # Paramodulations                      : 239
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 47
% 0.13/0.38  #    Positive orientable unit clauses  : 7
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 38
% 0.13/0.38  # Current number of unprocessed clauses: 204
% 0.13/0.38  # ...number of literals in the above   : 1876
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 18
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1297
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 171
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.38  # Unit Clause-clause subsumption calls : 14
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 13033
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.038 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.045 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
