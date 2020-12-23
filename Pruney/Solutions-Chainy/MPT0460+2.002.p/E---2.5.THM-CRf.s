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
% DateTime   : Thu Dec  3 10:48:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 113 expanded)
%              Number of clauses        :   24 (  42 expanded)
%              Number of leaves         :    5 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 548 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relat_1])).

fof(c_0_6,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X28,X31] :
      ( ( r2_hidden(k4_tarski(X23,esk4_5(X20,X21,X22,X23,X24)),X20)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk4_5(X20,X21,X22,X23,X24),X24),X21)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X26,X28),X20)
        | ~ r2_hidden(k4_tarski(X28,X27),X21)
        | r2_hidden(k4_tarski(X26,X27),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22)),X22)
        | ~ r2_hidden(k4_tarski(esk5_3(X20,X21,X22),X31),X20)
        | ~ r2_hidden(k4_tarski(X31,esk6_3(X20,X21,X22)),X21)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk7_3(X20,X21,X22)),X20)
        | r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk7_3(X20,X21,X22),esk6_3(X20,X21,X22)),X21)
        | r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_relat_1(X34)
      | v1_relat_1(k5_relat_1(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & v1_relat_1(esk10_0)
    & r1_tarski(esk8_0,esk9_0)
    & ~ r1_tarski(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X13)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X17)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),k5_relat_1(esk10_0,esk8_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X5)
    | ~ r2_hidden(k4_tarski(esk4_5(X3,X5,k5_relat_1(X3,X5),X1,X6),X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X6),k5_relat_1(X3,X5)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),k5_relat_1(esk10_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_11]),c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),X1),k5_relat_1(esk10_0,X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk4_5(esk10_0,esk8_0,k5_relat_1(esk10_0,esk8_0),esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20]),c_0_19])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_5(X1,esk8_0,k5_relat_1(X1,esk8_0),X2,X3),X3),esk9_0)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19])])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),k5_relat_1(esk10_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_20]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk10_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_11]),c_0_19]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:47:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.47  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.028 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t48_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.19/0.47  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.19/0.47  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.47  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.19/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.47  fof(c_0_5, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))))))), inference(assume_negation,[status(cth)],[t48_relat_1])).
% 0.19/0.47  fof(c_0_6, plain, ![X20, X21, X22, X23, X24, X26, X27, X28, X31]:((((r2_hidden(k4_tarski(X23,esk4_5(X20,X21,X22,X23,X24)),X20)|~r2_hidden(k4_tarski(X23,X24),X22)|X22!=k5_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)|~v1_relat_1(X20))&(r2_hidden(k4_tarski(esk4_5(X20,X21,X22,X23,X24),X24),X21)|~r2_hidden(k4_tarski(X23,X24),X22)|X22!=k5_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)|~v1_relat_1(X20)))&(~r2_hidden(k4_tarski(X26,X28),X20)|~r2_hidden(k4_tarski(X28,X27),X21)|r2_hidden(k4_tarski(X26,X27),X22)|X22!=k5_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)|~v1_relat_1(X20)))&((~r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22)),X22)|(~r2_hidden(k4_tarski(esk5_3(X20,X21,X22),X31),X20)|~r2_hidden(k4_tarski(X31,esk6_3(X20,X21,X22)),X21))|X22=k5_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)|~v1_relat_1(X20))&((r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk7_3(X20,X21,X22)),X20)|r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22)),X22)|X22=k5_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)|~v1_relat_1(X20))&(r2_hidden(k4_tarski(esk7_3(X20,X21,X22),esk6_3(X20,X21,X22)),X21)|r2_hidden(k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22)),X22)|X22=k5_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)|~v1_relat_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.19/0.47  fof(c_0_7, plain, ![X33, X34]:(~v1_relat_1(X33)|~v1_relat_1(X34)|v1_relat_1(k5_relat_1(X33,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.47  fof(c_0_8, negated_conjecture, (v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&(v1_relat_1(esk10_0)&(r1_tarski(esk8_0,esk9_0)&~r1_tarski(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.47  fof(c_0_9, plain, ![X13, X14, X15, X16, X17]:((~r1_tarski(X13,X14)|(~r2_hidden(k4_tarski(X15,X16),X13)|r2_hidden(k4_tarski(X15,X16),X14))|~v1_relat_1(X13))&((r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X13)|r1_tarski(X13,X17)|~v1_relat_1(X13))&(~r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X17)|r1_tarski(X13,X17)|~v1_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.19/0.47  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.47  cnf(c_0_11, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.47  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.47  cnf(c_0_13, negated_conjecture, (~r1_tarski(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.47  fof(c_0_15, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.47  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~v1_relat_1(X4)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])).
% 0.19/0.47  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,esk4_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_11])).
% 0.19/0.47  cnf(c_0_18, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),k5_relat_1(esk10_0,esk8_0))|~v1_relat_1(k5_relat_1(esk10_0,esk8_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.47  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_22, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.47  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X5)|~r2_hidden(k4_tarski(esk4_5(X3,X5,k5_relat_1(X3,X5),X1,X6),X2),X4)|~r2_hidden(k4_tarski(X1,X6),k5_relat_1(X3,X5))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.47  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),k5_relat_1(esk10_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_11]), c_0_19]), c_0_20])])).
% 0.19/0.47  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.47  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_11])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),X1),k5_relat_1(esk10_0,X2))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk4_5(esk10_0,esk8_0,k5_relat_1(esk10_0,esk8_0),esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20]), c_0_19])])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk4_5(X1,esk8_0,k5_relat_1(X1,esk8_0),X2,X3),X3),esk9_0)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19])])).
% 0.19/0.47  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0)),esk3_2(k5_relat_1(esk10_0,esk8_0),k5_relat_1(esk10_0,esk9_0))),k5_relat_1(esk10_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_20]), c_0_25])])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (~v1_relat_1(k5_relat_1(esk10_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_13])).
% 0.19/0.47  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_11]), c_0_19]), c_0_20])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 35
% 0.19/0.47  # Proof object clause steps            : 24
% 0.19/0.47  # Proof object formula steps           : 11
% 0.19/0.47  # Proof object conjectures             : 16
% 0.19/0.47  # Proof object clause conjectures      : 13
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 12
% 0.19/0.47  # Proof object initial formulas used   : 5
% 0.19/0.47  # Proof object generating inferences   : 9
% 0.19/0.47  # Proof object simplifying inferences  : 22
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 5
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 18
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 18
% 0.19/0.47  # Processed clauses                    : 442
% 0.19/0.47  # ...of these trivial                  : 0
% 0.19/0.47  # ...subsumed                          : 276
% 0.19/0.47  # ...remaining for further processing  : 166
% 0.19/0.47  # Other redundant clauses eliminated   : 3
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 7
% 0.19/0.47  # Backward-rewritten                   : 1
% 0.19/0.47  # Generated clauses                    : 3010
% 0.19/0.47  # ...of the previous two non-trivial   : 2947
% 0.19/0.47  # Contextual simplify-reflections      : 9
% 0.19/0.47  # Paramodulations                      : 2965
% 0.19/0.47  # Factorizations                       : 42
% 0.19/0.47  # Equation resolutions                 : 3
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 138
% 0.19/0.47  #    Positive orientable unit clauses  : 7
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 2
% 0.19/0.47  #    Non-unit-clauses                  : 129
% 0.19/0.47  # Current number of unprocessed clauses: 2540
% 0.19/0.47  # ...number of literals in the above   : 16967
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 25
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 10403
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 3271
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 292
% 0.19/0.47  # Unit Clause-clause subsumption calls : 14
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 1
% 0.19/0.47  # BW rewrite match successes           : 1
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 71172
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.125 s
% 0.19/0.47  # System time              : 0.007 s
% 0.19/0.47  # Total time               : 0.132 s
% 0.19/0.47  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
